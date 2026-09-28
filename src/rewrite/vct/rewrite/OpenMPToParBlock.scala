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

  case class Clauses(
      privateVars: Seq[String] = Nil,
      firstPrivateVars: Seq[String] = Nil,
      reduction: Option[(String, Seq[String])] = None,
      isNowait: Boolean = false,
      isStaticSchedule: Boolean = false,
  )

  object Clauses {
    val onFor: collection.Set[String] = collection.Set(
      "private",
      "firstprivate",
      "shared",
      "reduction",
      "schedule",
      "nowait",
      "numthreads",
    )

    val onParallel: collection.Set[String] = collection.Set(
      "shared",
      "numthreads",
    )

    val onSections: collection.Set[String] = collection.Set.empty

    val hint: String =
      "VerCors translates `shared`, `num_threads`, `private`, `firstprivate`, " +
        "`reduction(+)`, `schedule(static)` and `nowait` clauses of `omp for` loops, " +
        "and only `shared` and `num_threads` clauses of `omp parallel` regions."
  }

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
      clauses: Clauses,
      o: Origin,
      blame: Blame[ParBlockFailure],
  ) extends PPL[G] {
    override def hasStaticSchedule: Boolean = clauses.isStaticSchedule
    override def isNoWait: Boolean = clauses.isNowait
    override def isFor: Boolean = v.nonEmpty
    override def origin: Origin = o
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
    override def origin: Origin = o
  }

  case class PPLFuse[G](p1: PPL[G], p2: PPL[G]) extends PPL[G] {
    override val hasStaticSchedule: Boolean =
      p1.hasStaticSchedule && p2.hasStaticSchedule
    override val isNoWait: Boolean = p1.isNoWait && p2.isNoWait
    override val isFor: Boolean = false
    override def origin: Origin = p1.origin
  }

  case class CannotTranslateToParBlock(o: Origin, message: String)
      extends UserError {
    override def code: String = "cannotTranslateOpenMP"
    override def text: String = o.messageInContext(message)
  }
}

case class OpenMPToParBlock[Pre <: Generation]() extends Rewriter[Pre] {
  import OpenMPToParBlock._

  private def fail(node: Node[_], message: String): Nothing =
    fail(node.o, message)

  private def fail(o: Origin, message: String): Nothing =
    throw CannotTranslateToParBlock(o, message)

  private def sameName(decl: Declaration[Pre], name: String): Boolean =
    decl.o.getPreferredNameOrElse().camel == name

  private def statementsOf(impl: Statement[Pre]): Seq[Statement[Pre]] =
    impl match {
      case Block(stats) => stats
      case other        => Seq(other)
    }

  override def dispatch(stat: Statement[Pre]): Statement[Post] =
    stat match {
      case omp @ OmpParallel(block, clauses) =>
        checkClauses(omp, clauses, "an `omp parallel` region", Clauses.onParallel)
        val (regionVars, ppl) = translateRegion(block, omp.o, omp.blame)
        checkWritableScope(omp, ppl)
        val parStatement = pplToStatement(ppl, omp.blame)
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

      case omp @ OmpSections(ompBlock, clauses) =>
        checkClauses(omp, clauses, "an `omp sections` region", Clauses.onSections)
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
        sections.reduceLeftOption { (a, b) =>
          PPLPar[Pre](a, b, omp.o)
        }.getOrElse(
          fail(omp, "An omp sections block must contain at least one omp section.")
        )

      case omp @ OmpParallel(block, clauses) =>
        checkClauses(omp, clauses, "an `omp parallel` region", Clauses.onParallel)
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

  private val clauseRegex = """(\w+)(?:\((.*)\))?""".r
  private val reductionRegex = """(.*?):(.*)""".r

  def checkClauses(
      node: Node[_],
      clauses: Seq[String],
      construct: String,
      supported: collection.Set[String],
  ): Clauses =
    clauses.foldLeft(Clauses()) { (acc, clause) =>
      val (name, args) = clause match {
        case clauseRegex(name, args) =>
          val names = Option(args).getOrElse("")
          (name, names.split(",").map(_.trim).filter(_.nonEmpty).toSeq)
        case _ =>
          fail(node, s"The clause `$clause` on $construct could not be parsed.")
      }
      if (!supported.contains(name))
        fail(node, s"The clause `$clause` on $construct is not supported. ${Clauses.hint}")
      (name, args) match {
        case ("private", names)          => acc.copy(privateVars = names)
        case ("firstprivate", names)     => acc.copy(firstPrivateVars = names)
        case ("schedule", Seq("static")) => acc.copy(isStaticSchedule = true)
        case ("nowait", _)               => acc.copy(isNowait = true)
        case ("reduction", Seq(argument)) =>
          acc.copy(reduction = Some(parseReduction(node, construct, argument)))
        case ("shared", _) | ("numthreads", _) => acc
        case _ => fail(node, s"The clause `$clause` on $construct is not supported.")
      }
    }

  private def parseReduction(
      node: Node[_],
      construct: String,
      argument: String,
  ): (String, Seq[String]) =
    argument match {
      case reductionRegex(op, _) if op.trim != "+" =>
        fail(
          node,
          s"Only `reduction(+:...)` is supported, but $construct has a `reduction($op:...)` clause.",
        )
      case reductionRegex("+", names) =>
        ("+", names.split(",").map(_.trim).filter(_.nonEmpty).toSeq)
      case _ =>
        fail(node, s"The `reduction(...)` clause on $construct could not be parsed.")
    }

  def findSharedVariable(
      name: String,
      nodes: Seq[Node[Pre]],
      local: collection.Set[Declaration[Pre]],
  ): Option[Expr[Pre]] =
    nodes.iterator.flatMap(
      _.collectFirst {
        case e: Local[Pre] if sameName(e.ref.decl, name) && !local.contains(e.ref.decl) => e
        case e: DerefHeapVariable[Pre] if sameName(e.ref.decl, name) && !local.contains(e.ref.decl) => e
      }
    ).toSeq.headOption

  private def localOf(e: Expr[Pre]): Option[Variable[Pre]] = e match {
    case Local(Ref(v)) => Some(v)
    case _             => None
  }

  private def assignedVariable(node: Node[Pre]): Option[Variable[Pre]] = node match {
    case Assign(target, _)               => localOf(target)
    case AssignInitial(target, _)        => localOf(target)
    case PreAssignExpression(target, _)  => localOf(target)
    case PostAssignExpression(target, _) => localOf(target)
    case _                               => None
  }

  def contentWrites(
      content: Statement[Pre],
  ): (Set[Variable[Pre]], Set[Variable[Pre]]) = {
    val writes = mutable.Set[Variable[Pre]]()
    val declaresInside = mutable.Set[Variable[Pre]]()
    def rec(node: Node[Pre]): Unit =
      node match {
        case LocalDecl(v) => declaresInside += v
        case Scope(vars, inner) =>
          vars.foreach(declaresInside += _)
          rec(inner)
        case other =>
          assignedVariable(other).foreach(writes += _)
          other.subnodes.foreach(rec)
      }
    rec(content)
    (writes.toSet, declaresInside.toSet)
  }

  private def reductionVariables(block: PPLBlock[Pre]): Set[Variable[Pre]] =
    unfoldStar(block.requires).collect {
      case Reducible(Local(Ref(v)), _) => v
    }.toSet


  def checkWritableScope(
      container: Node[_],
      ppl: PPL[Pre],
  ): Unit =
    foldBlocks(ppl) { block =>
      val (writes, declaresInside) = contentWrites(block.content)
      val invalid =
        writes -- declaresInside -- block.v.toSet -- reductionVariables(block)
      if (invalid.nonEmpty) {
        val names = invalid.iterator
          .map(v => v.o.getPreferredNameOrElse().camel)
          .toSeq
          .sorted
          .mkString(", ")
        fail(
          container,
          s"The OpenMP region writes to $names, which it shares with the enclosing scope. " +
            "A parallel region may only be verified when it leaves such variables alone, " +
            "reduces them with a `reduction(...)` clause, or writes to a `private(...)` or " +
            "`firstprivate(...)` copy of them.",
        )
      }
    }

  def makePrivate(
      body: Statement[Pre],
      clauses: Clauses,
      iterVar: Variable[Pre],
      node: Node[_],
  ): Statement[Pre] = {
    val local = mutable.Set[Declaration[Pre]]() ++= contentWrites(body)._2
    val copies = clauses.privateVars.map(name => (name, false)) ++
      clauses.firstPrivateVars.map(name => (name, true))
    copies.foldLeft(body) { case (current, (name, initialize)) =>
      if (sameName(iterVar, name)) current
      else {
        val res = findSharedVariable(name, Seq(current), local.toSet).getOrElse(
          fail(
            node,
            s"The clause mentions `$name`, but no such variable is in scope outside the " +
              "`omp for` loop. Variables that the loop body declares itself are already " +
              "thread-local and need no clause.",
          )
        )
        local ++= localOf(res)
        threadLocal(current, res, initialize)
      }
    }
  }

  private def threadLocal(
      content: Statement[Pre],
      res: Expr[Pre],
      initialize: Boolean,
  ): Statement[Pre] = {
    implicit val o: Origin = res.o
    val original = localOf(res).get
    val fresh = new Variable[Pre](original.t)(original.o)
    val renamed: Statement[Pre] = new Substitute[Pre](
      Map(res -> Local[Pre](fresh.ref)),
      bindingSubs = Map(original -> fresh),
    ).dispatch(content): Statement[Pre]
    val body =
      if (initialize)
        Block(Seq(assignLocal(Local[Pre](fresh.ref), res), renamed))
      else renamed
    Scope[Pre](Seq(fresh), body)
  }

  def loopToPPL(
      loop: Loop[Pre],
      clauses: Seq[String],
      blame: Blame[ParBlockFailure],
  ): PPLBlock[Pre] =
    loop.contract match {
      case it: IterationContract[Pre] =>
        val parsed = checkClauses(loop, clauses, "an `omp for` loop", Clauses.onFor)
        val (v, from, to) = extractLoopData(loop)
        val block = PPLBlock[Pre](
          v = Some(v),
          from = Some(from),
          to = Some(to),
          context = it.context_everywhere,
          requires = it.requires,
          ensures = it.ensures,
          content = makePrivate(loop.body, parsed, v, loop),
          clauses = parsed,
          o = loop.o,
          blame = blame,
        )
        parsed.reduction.fold(block) { case (op, names) =>
          withReductions(block, op, names)
        }
      case _ =>
        fail(loop, "An omp for loop must have a loop contract with context/ensures clauses.")
    }

  def withReductions(
      block: PPLBlock[Pre],
      op: String,
      names: Seq[String],
  ): PPLBlock[Pre] = {
    implicit val o: Origin = block.o
    val declaredInside: collection.Set[Declaration[Pre]] =
      contentWrites(block.content)._2.map(v => v: Declaration[Pre])
    val reducible = names.map { name =>
      findSharedVariable(
        name,
        Seq(block.requires, block.ensures, block.content),
        declaredInside,
      ).getOrElse(
        fail(
          block.o,
          s"The reduction clause mentions `$name`, but no such variable is in scope in the " +
            "`omp parallel` region. A reduction variable is shared with the enclosing scope, " +
            "so it cannot be declared inside the loop body.",
        )
      )
    }
    block.copy(
      requires =
        reducible.foldLeft(block.requires)((acc, res) => acc &* Reducible(res, op)),
    )
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
    PPLBlock[Pre](
      v = None,
      from = None,
      to = None,
      context = tt,
      requires = tt,
      ensures = tt,
      content = stat,
      clauses = Clauses(),
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
      .getOrElse(
        plainToPPL(Block[Pre](Nil)(defaultOrigin), defaultOrigin, defaultBlame)
      )
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

  def foldBlocks(ppl: PPL[Pre])(visit: PPLBlock[Pre] => Unit): Unit =
    ppl match {
      case block: PPLBlock[Pre] => visit(block)
      case PPLSeq(a, b, _)      => foldBlocks(a)(visit); foldBlocks(b)(visit)
      case PPLPar(a, b, _)      => foldBlocks(a)(visit); foldBlocks(b)(visit)
      case fused: PPLFuse[Pre]  => foldBlocks(fused.p1)(visit); foldBlocks(fused.p2)(visit)
    }

  def commonParts(a: Expr[Pre], b: Expr[Pre]): Expr[Pre] = {
    implicit val o: Origin = a.o
    foldStar(unfoldStar(a).toSet.intersect(unfoldStar(b).toSet).toSeq)
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
    PPLBlock[Pre](
      v = x.v,
      from = x.from,
      to = x.to,
      context = tt,
      requires = mergeContext(
        x.requires,
        sub.dispatch(commonParts(y.requires, y.ensures)),
      ),
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