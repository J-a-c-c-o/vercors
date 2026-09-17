package vct.col.rewrite

import vct.col.ast._
import vct.col.origin._
import vct.col.ref.Ref
import vct.col.util.AstBuildHelpers._
import vct.col.util.Substitute
import vct.result.VerificationError.UserError

import scala.collection.mutable

case object OpenMPToParBlock extends RewriterBuilder {
  override def key: String = "openmp"
  override def desc: String =
    "Translate OpenMP parallel regions to parallel blocks."

  sealed trait PPL[G] {
    def hasStaticSchedule: Boolean
    def isNoWait: Boolean
    def isFor: Boolean
    def origin: Origin
  }

  case class PPLBlock[G](
      v: Option[Variable[G]],
      from: Option[Expr[G]],
      to: Option[Expr[G]],
      context: Expr[G],
      requires: Expr[G],
      ensures: Expr[G],
      content: Statement[G],
      clauses: Seq[String],
      o: Origin,
      blame: Blame[ParBlockFailure],
  ) extends PPL[G] {
    override val hasStaticSchedule: Boolean =
      clauses.contains("schedule(static)")
    override val isNoWait: Boolean = clauses.contains("nowait")
    override val isFor: Boolean = v.nonEmpty
    override val origin: Origin = o
  }

  case class PPLSeq[G](p1: PPL[G], p2: PPL[G], o: Origin) extends PPL[G] {
    override val hasStaticSchedule: Boolean =
      p1.hasStaticSchedule && p2.hasStaticSchedule
    override val isNoWait: Boolean = p1.isNoWait && p2.isNoWait
    override val isFor: Boolean = false
    override val origin: Origin = o
  }

  case class PPLPar[G](p1: PPL[G], p2: PPL[G], o: Origin) extends PPL[G] {
    override val hasStaticSchedule: Boolean =
      p1.hasStaticSchedule && p2.hasStaticSchedule
    override val isNoWait: Boolean = p1.isNoWait && p2.isNoWait
    override val isFor: Boolean = false
    override val origin: Origin = o
  }

  case class PPLFuse[G](p1: PPL[G], p2: PPL[G]) extends PPL[G] {
    override val hasStaticSchedule: Boolean =
      p1.hasStaticSchedule && p2.hasStaticSchedule
    override val isNoWait: Boolean = p1.isNoWait && p2.isNoWait
    override val isFor: Boolean = false
    override val origin: Origin = p1.origin
  }

  case class CannotTranslateToParBlock(node: Node[_], message: String)
      extends UserError {
    override def code: String = "cannotTranslateOpenMP"
    override def text: String = node.o.messageInContext(message)
  }
}

case class OpenMPToParBlock[Pre <: Generation]() extends Rewriter[Pre] {
  import OpenMPToParBlock._

  private def fail(node: Node[_], message: String): Nothing =
    throw CannotTranslateToParBlock(node, message)

  private def sameName(decl: Declaration[Pre], name: String): Boolean =
    decl.o.getPreferredNameOrElse().camel.equalsIgnoreCase(name)

  private def statementsOf(impl: Statement[Pre]): Seq[Statement[Pre]] =
    impl match {
      case Block(stats) => stats
      case other        => Seq(other)
    }

  private def emptyBlock(
      origin: Origin,
      blame: Blame[ParBlockFailure],
  ): PPLBlock[Pre] =
    PPLBlock(
      v = None,
      from = None,
      to = None,
      context = tt,
      requires = tt,
      ensures = tt,
      content = Block[Pre](Nil)(origin),
      clauses = Nil,
      o = origin,
      blame = blame,
    )

  override def dispatch(stat: Statement[Pre]): Statement[Post] =
    stat match {
      case omp @ OmpParallel(block, _) =>
        val (regionVars, ppl) = translateRegion(block, omp.o, omp.blame)
        val withReductions = applyReductions(ppl, omp, block)
        checkWritableScope(omp, withReductions)
        val parStatement = pplToStatement(withReductions, omp.blame)
        if (regionVars.nonEmpty)
          Scope[Post](regionVars, parStatement)(omp.o)
        else
          parStatement

      case omp: OmpFor[Pre] =>
        fail(omp, "This omp for is not inside an omp parallel block.")
      case omp: OmpSections[Pre] =>
        fail(omp, "This omp sections is not inside an omp parallel block.")
      case omp: OmpSection[Pre] =>
        fail(omp, "This omp section is not inside an omp sections block.")
      case other => rewriteDefault(other)
    }

  def translateRegion(
      block: Statement[Pre],
      origin: Origin,
      blame: Blame[ParBlockFailure],
  ): (Seq[Variable[Post]], PPL[Pre]) = {
    val (declaredVars, stats) = block match {
      case Scope(vars, impl) =>
        val newVars = variables.collect {
          vars.foreach(v => variables.succeed(v, v.rewrite()))
        }._1
        (newVars, statementsOf(impl))
      case Block(stats) => (Nil, stats)
      case other        => (Nil, Seq(other))
    }
    val hoisted = mutable.ListBuffer[Variable[Post]]()
    val ppLs: Seq[PPL[Pre]] = stats.flatMap {
      case LocalDecl(local) =>
        hoisted ++= variables.collect {
          variables.succeed(local, local.rewrite())
        }._1
        None
      case Block(Nil) => None
      case stat       => Some(matchNode(stat, origin, blame))
    }
    (declaredVars ++ hoisted, compose(ppLs, origin, blame))
  }

  def matchNode(
      stat: Statement[Pre],
      defaultOrigin: Origin,
      defaultBlame: Blame[ParBlockFailure],
  ): PPL[Pre] =
    stat match {
      case omp @ OmpFor(wrapped, clauses) =>
        val loop: Loop[Pre] = unwrapToLoop(wrapped).getOrElse(
          fail(wrapped, "An omp for must precede a for loop.")
        )
        loopToPPL(loop, clauses, omp.blame)

      case omp @ OmpSections(ompBlock, _) =>
        val sections: Seq[PPL[Pre]] = extractBlock(ompBlock, omp).map {
          case OmpSection(sectionBlock) =>
            val (vars, ppl) =
              translateRegion(sectionBlock, sectionBlock.o, omp.blame)
            if (vars.nonEmpty)
              fail(
                sectionBlock,
                "OpenMP `section` blocks can only be verified when they consist purely of `for` " +
                  "loops; thread-local declarations inside them are not supported.",
              )
            ppl
          case other =>
            fail(other, "An omp sections block may only contain omp section blocks.")
        }
        sections.reduceLeft { (a, b) =>
          PPLPar[Pre](a, b, omp.o)
        }

      case omp @ OmpParallel(block, _) =>
        translateRegion(block, omp.o, omp.blame)._2

      case other =>
        plainToPPL(other, defaultOrigin, defaultBlame)
    }

  def extractBlock(
      block: Statement[Pre],
      container: Node[_],
  ): Seq[Statement[Pre]] =
    block match {
      case Scope(vars, Block(stats)) =>
        if (vars.nonEmpty)
          fail(
            block,
            "OpenMP `sections` regions can only be verified when they consist purely of `section` " +
              "blocks; clauses declaring variables are not supported.",
          )
        stats
      case _ =>
        fail(container, "Expected a block statement.")
    }

  def reductionClause(
      clauses: Seq[String],
  ): Option[(String, Seq[String])] =
    clauses.collectFirst {
      case c if c.startsWith("reduction(") =>
        val rest = c.stripPrefix("reduction(").stripSuffix(")")
        val (op, ids) = rest.span(_ != ':')
        (op.trim, ids.drop(1).split(",").map(_.trim).toSeq)
    }

  def ompReductionClauses(
      stmt: Statement[Pre],
  ): Seq[(String, Seq[String])] = {
    val result = mutable.ListBuffer[(String, Seq[String])]()
    def rec(s: Statement[Pre]): Unit =
      s match {
        case Scope(_, inner) =>
          rec(inner)
        case Block(stats) =>
          stats.foreach(rec)
        case OmpFor(_, clauses) =>
          result ++= reductionClause(clauses).toSeq
        case OmpParallel(_, clauses) =>
          result ++= reductionClause(clauses).toSeq
        case _ =>
      }
    rec(stmt)
    result.toSeq
  }

  def applyReductions(
      ppl: PPL[Pre],
      container: Node[_],
      region: Statement[Pre],
  ): PPL[Pre] =
    ompReductionClauses(region).foldLeft(ppl) { case (p, (op, names)) =>
      names.foldLeft(p) { case (pp, name) =>
        val res: Expr[Pre] = findReductionVariable(name, region).getOrElse(
          fail(
            container,
            s"The reduction clause mentions $name, but we could not find such a variable in the parallel block.",
          )
        )
        withReduction(pp, op, res)
      }
    }

  def findReductionVariable(
      name: String,
      block: Statement[Pre],
  ): Option[Expr[Pre]] = {
    var result: Option[Expr[Pre]] = None
    block.foreach {
      case l: Local[Pre] if sameName(l.ref.decl, name) =>
        result = Some(l)
      case d @ DerefHeapVariable(Ref(decl)) if sameName(decl, name) =>
        result = Some(d)
      case _ =>
    }
    result
  }

  def findVariable(
      name: String,
      content: Statement[Pre],
  ): Option[Variable[Pre]] = {
    var result: Option[Variable[Pre]] = None
    content.foreach {
      case l: Local[Pre] if sameName(l.ref.decl, name) =>
        result = Some(l.ref.decl)
      case _ =>
    }
    result
  }

  def usesExpr(
      content: Statement[Pre],
      res: Expr[Pre],
  ): Boolean = {
    var uses = false
    content.foreach {
      case e: Expr[Pre] if e == res => uses = true
      case _                        =>
    }
    uses
  }

  def mapPPLBlocks(
      ppl: PPL[Pre]
  )(f: PPLBlock[Pre] => PPLBlock[Pre]): PPL[Pre] =
    ppl match {
      case block: PPLBlock[Pre] => f(block)
      case PPLSeq(a, b, o)      => PPLSeq(mapPPLBlocks(a)(f), mapPPLBlocks(b)(f), o)
      case PPLPar(a, b, o)      => PPLPar(mapPPLBlocks(a)(f), mapPPLBlocks(b)(f), o)
      case fused: PPLFuse[Pre]  => PPLFuse(mapPPLBlocks(fused.p1)(f), mapPPLBlocks(fused.p2)(f))
    }

  def foldPPL(ppl: PPL[Pre])(visit: PPLBlock[Pre] => Unit): Unit =
    ppl match {
      case block: PPLBlock[Pre] => visit(block)
      case PPLSeq(a, b, _)      => foldPPL(a)(visit); foldPPL(b)(visit)
      case PPLPar(a, b, _)      => foldPPL(a)(visit); foldPPL(b)(visit)
      case fused: PPLFuse[Pre]  => foldPPL(fused.p1)(visit); foldPPL(fused.p2)(visit)
    }

  def withReduction(
      ppl: PPL[Pre],
      op: String,
      res: Expr[Pre],
  ): PPL[Pre] =
    mapPPLBlocks(ppl) { block =>
      if (usesExpr(block.content, res)) {
        implicit val o: Origin = block.o
        block.copy(requires = block.requires &* Reducible(res, op)(o))
      } else block
    }

  def checkWritableScope(
      container: Node[_],
      ppl: PPL[Pre],
  ): Unit =
    foldPPL(ppl) { block =>
      val (writes, declaresInside) = contentWrites(block.content)
      val invalid = writes -- declaresInside -- block.v.toSet
      if (invalid.nonEmpty) {
        val names = invalid.iterator
          .map(v => v.o.getPreferredNameOrElse().camel)
          .toSeq
          .sorted
          .mkString(", ")
        fail(
          container,
          s"OpenMP parallel regions can only be verified when they consist purely of `for` loops and `sections`, " +
            s"without thread-local declarations ($names).",
        )
      }
    }

  def contentWrites(
      content: Statement[Pre],
  ): (Set[Variable[Pre]], Set[Variable[Pre]]) = {
    val writes = mutable.Set[Variable[Pre]]()
    val declaresInside = mutable.Set[Variable[Pre]]()
    def rec(s: Statement[Pre]): Unit =
      s match {
        case Assign(Local(Ref(v)), _) =>
          writes += v
        case LocalDecl(v) =>
          declaresInside += v
        case Scope(vars, inner) =>
          vars.foreach(declaresInside += _)
          rec(inner)
        case Block(stats) =>
          stats.foreach(rec)
        case other =>
          other.subnodes.foreach {
            case s2: Statement[Pre] => rec(s2)
            case _                  =>
          }
      }
    rec(content)
    (writes.toSet, declaresInside.toSet)
  }

  def clauseNames(
      clauses: Seq[String],
      key: String,
  ): Seq[String] =
    clauses.collectFirst {
      case c if c.startsWith(key) =>
        c.stripPrefix(key).stripSuffix(")").split(",").map(_.trim).toSeq
    }.getOrElse(Nil)

  def privateVariables(clauses: Seq[String]): Seq[String] =
    clauseNames(clauses, "private(")

  def firstPrivateVariables(clauses: Seq[String]): Seq[String] =
    clauseNames(clauses, "firstprivate(")

  def makePrivateVars(
      content: Statement[Pre],
      names: Seq[String],
      iterVar: Option[Variable[Pre]],
      initialize: Boolean,
  ): Statement[Pre] =
    names.foldLeft(content) { case (current, name) =>
      if (iterVar.exists(sameName(_, name))) current
      else
        findVariable(name, current) match {
          case Some(v) =>
            implicit val o: Origin = v.o
            val fresh = new Variable[Pre](v.t)(v.o)
            val rewritten: Statement[Pre] =
              new Substitute[Pre](
                Map(
                  Local[Pre](v.ref[Variable[Pre]]) -> Local[Pre](fresh.ref)
                ),
                bindingSubs = Map(v -> fresh),
              ).dispatch(current) match {
                case s: Statement[Pre] => s
              }
            val body: Statement[Pre] =
              if (initialize)
                Block(Seq(
                  assignLocal(
                    Local[Pre](fresh.ref),
                    Local[Pre](v.ref[Variable[Pre]]),
                  ),
                  rewritten,
                ))
              else
                rewritten
            Scope[Pre](Seq(fresh), body)(v.o)
          case None => current
        }
    }

  def makePrivate(
      content: Statement[Pre],
      clauses: Seq[String],
      iterVar: Option[Variable[Pre]],
  ): Statement[Pre] = {
    val withPrivate =
      makePrivateVars(content, privateVariables(clauses), iterVar, initialize = false)
    makePrivateVars(content = withPrivate, firstPrivateVariables(clauses), iterVar, initialize = true)
  }

  def loopToPPL(
      loop: Loop[Pre],
      clauses: Seq[String],
      blame: Blame[ParBlockFailure],
  ): PPLBlock[Pre] =
    loop.contract match {
      case it: IterationContract[Pre] =>
        val (v, from, to) = extractLoopData(loop)
        val context = contextPart(it)
        PPLBlock(
          v = Some(v),
          from = Some(from),
          to = Some(to),
          context = context,
          requires = stripContext(it.requires, context),
          ensures = stripContext(it.ensures, context),
          content = makePrivate(loop.body, clauses, Some(v)),
          clauses = clauses,
          o = loop.o,
          blame = blame,
        )
      case _ =>
        fail(loop, "An omp for loop must have a loop contract with context/ensures clauses.")
    }

  def contextPart(it: IterationContract[Pre]): Expr[Pre] = {
    implicit val o: Origin = it.o
    val contextParts =
      unfoldStar(it.requires).toSet.intersect(unfoldStar(it.ensures).toSet)
    foldStar(contextParts.toSeq)
  }

  def stripContext(expr: Expr[Pre], context: Expr[Pre]): Expr[Pre] = {
    implicit val o: Origin = expr.o
    val contextParts = unfoldStar(context).toSet
    foldStar(unfoldStar(expr).filterNot(contextParts).toSeq)
  }

  private def unwrapToLoop(stat: Statement[Pre]): Option[Loop[Pre]] =
    stat match {
      case l: Loop[Pre]      => Some(l)
      case Scope(_, inner)   => unwrapToLoop(inner)
      case Block(Seq(inner)) => unwrapToLoop(inner)
      case _                 => None
    }

  def extractLoopData(
      loop: Loop[Pre],
  ): (Variable[Pre], Expr[Pre], Expr[Pre]) = {
    implicit val o: Origin = loop.o
    val (v, from) = firstInitAssign(loop.init).getOrElse(
      fail(
        loop,
        "we could not derive the iteration variable or its lower bound from the initialization portion of the loop",
      )
    )
    val to = exclusiveUpperBound(v, loop.cond).getOrElse(
      fail(
        loop,
        "we could not derive an upper bound for the iteration variable from the condition",
      )
    )
    if (!loop.doesIncrement(v))
      fail(
        loop,
        "we could not ascertain that the iteration variable is incremented by one each iteration",
      )
    (v, from, to)
  }

  private def firstInitAssign(
      init: Statement[Pre],
  ): Option[(Variable[Pre], Expr[Pre])] =
    init match {
      case Block(stats) =>
        stats
          .flatMap(s => firstInitAssign(s).toSeq)
          .headOption
      case Assign(Local(Ref(v)), low) => Some((v, low))
      case Eval(PreAssignExpression(Local(Ref(v)), low)) => Some((v, low))
      case _ => None
    }

  private def exclusiveUpperBound(
      v: Variable[Pre],
      cond: Expr[Pre],
  )(implicit o: Origin): Option[Expr[Pre]] =
    cond match {
      case Less(Local(Ref(`v`)), high)      => Some(high)
      case LessEq(Local(Ref(`v`)), high)    => Some(high + const(1))
      case Greater(high, Local(Ref(`v`)))   => Some(high)
      case GreaterEq(high, Local(Ref(`v`))) => Some(high + const(1))
      case _                                => None
    }

  def plainToPPL(
      stat: Statement[Pre],
      origin: Origin,
      blame: Blame[ParBlockFailure],
  ): PPLBlock[Pre] = {
    implicit val o: Origin = origin
    PPLBlock(
      v = None,
      from = None,
      to = None,
      context = tt,
      requires = tt,
      ensures = tt,
      content = stat,
      clauses = Nil,
      o = origin,
      blame = blame,
    )
  }

  def compose(
      xs: Seq[PPL[Pre]],
      defaultOrigin: Origin,
      defaultBlame: Blame[ParBlockFailure],
  ): PPL[Pre] = {
    val fused = bundle[PPL[Pre]](
      (x, y) => PPLFuse[Pre](x, y),
      canFuse,
      xs,
    )
    val pared = bundle[PPL[Pre]](
      (x, y) => PPLPar[Pre](x, y, x.origin),
      (x, _) => x.isNoWait,
      fused,
    )
    pared
      .reduceLeftOption((a, b) => PPLSeq[Pre](a, b, a.origin))
      .getOrElse(emptyBlock(defaultOrigin, defaultBlame))
  }

  def canFuse(x: PPL[Pre], y: PPL[Pre]): Boolean =
    x.isFor && y.isFor && x.hasStaticSchedule && y.hasStaticSchedule && x.isNoWait

  def bundle[X](
      op: (X, X) => X,
      cond: (X, X) => Boolean,
      xs: Seq[X],
  ): Seq[X] =
    if (xs.isEmpty) xs
    else
      xs.init.foldRight(Seq(xs.last)) { (x, r) =>
        if (cond(x, r.head)) op(x, r.head) +: r.tail
        else x +: r
      }

  def mergeContext(a: Expr[Pre], b: Expr[Pre]): Expr[Pre] = {
    implicit val o: Origin = a.o
    val perms = mutable.LinkedHashMap[Location[Pre], Expr[Pre]]()
    val otherParts = mutable.LinkedHashSet[Expr[Pre]]()
    (unfoldStar(a) ++ unfoldStar(b)).foreach {
      case Perm(loc, amount) =>
        if (!perms.contains(loc))
          perms(loc) = amount
      case other =>
        if (other != tt)
          otherParts += other
    }
    foldStar(
      perms.map { case (loc, amount) => Perm[Pre](loc, amount) }.toSeq ++
        otherParts.toSeq
    )
  }

  def fuse(x: PPLBlock[Pre], y: PPLBlock[Pre]): PPLBlock[Pre] = {
    implicit val o: Origin = x.o
    val xv = x.v.get
    val yv = y.v.get
    val sub = new Substitute[Pre](
      Map[Expr[Pre], Expr[Pre]](
        Local(yv.ref[Variable[Pre]]) -> Local(xv.ref[Variable[Pre]])
      ),
      bindingSubs = Map(yv -> xv),
    )
    PPLBlock(
      v = x.v,
      from = x.from,
      to = x.to,
      context = mergeContext(x.context, sub.dispatch(y.context)),
      requires = x.requires,
      ensures = sub.dispatch(y.ensures),
      content = Block[Pre](Seq(x.content, sub.dispatch(y.content))),
      clauses = x.clauses,
      o = x.o,
      blame = x.blame,
    )
  }

  def pplToStatement(
      ppl: PPL[Pre],
      blame: Blame[ParBlockFailure],
  ): Statement[Post] =
    ppl match {
      case seq: PPLSeq[Pre] =>
        implicit val o: Origin = seq.origin
        Block(Seq(
          pplToStatement(seq.p1, blame),
          pplToStatement(seq.p2, blame),
        ))
      case other =>
        ParStatement(toParRegion(other, blame))(other.origin)
    }

  def toParRegion(
      ppl: PPL[Pre],
      defaultBlame: Blame[ParBlockFailure],
  ): ParRegion[Post] =
    ppl match {
      case block: PPLBlock[Pre] =>
        blockToRegion(block)
      case p: PPLFuse[Pre] =>
        toParRegion(
          fuse(p.p1.asInstanceOf[PPLBlock[Pre]], p.p2.asInstanceOf[PPLBlock[Pre]]),
          defaultBlame,
        )
      case seq: PPLSeq[Pre] =>
        implicit val o: Origin = seq.origin
        ParSequential[Post](
          Seq(toParRegion(seq.p1, defaultBlame), toParRegion(seq.p2, defaultBlame))
        )(defaultBlame)
      case par: PPLPar[Pre] =>
        implicit val o: Origin = par.origin
        ParParallel[Post](
          Seq(toParRegion(par.p1, defaultBlame), toParRegion(par.p2, defaultBlame))
        )(defaultBlame)
    }

  def blockToRegion(block: PPLBlock[Pre]): ParRegion[Post] = {
    implicit val o: Origin = block.o
    val iterOpt: Option[IterVariable[Post]] =
      for {
        v <- block.v
        f <- block.from
        t <- block.to
      } yield IterVariable(
        variables.freeze.computeSucc(v).getOrElse(variables.dispatch(v)),
        dispatch(f),
        dispatch(t),
      )

    sendDecls.scope {
      val (newVars, newContent) = variables.collect {
        dispatch(block.content)
      }
      val bodyScope = Scope[Post](newVars, newContent)(block.content.o)
      ParBlock[Post](
        decl = new ParBlockDecl[Post](),
        iters = iterOpt.toSeq,
        context_everywhere = dispatch(block.context),
        requires = dispatch(block.requires),
        ensures = dispatch(block.ensures),
        content = bodyScope,
      )(block.blame)
    }
  }
}