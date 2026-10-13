package vct.col.rewrite

import vct.col.ast._
import vct.result.VerificationError.UserError
import vct.col.origin.{LabelContext, Origin, PreferredName}
import vct.col.ref.{LazyRef, Ref}
import vct.col.rewrite.util.FreeVariables
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder, Rewritten}
import vct.col.check.CheckContext
import vct.col.util.AstBuildHelpers._
import vct.col.util.Substitute

import scala.collection.mutable

object SimplifyFoldsErrors {
  case class CannotFoldOverType(at: Origin, t: Type[_]) extends UserError {
    override def code: String = "foldUnsupportedType"
    override def text: String =
      at.messageInContext(s"A sum or product over a value of type $t is not supported")
  }

  case class CannotFoldOverLocation(at: Origin) extends UserError {
    override def code: String = "foldOverLocation"
    override def text: String = at.messageInContext(
      "A sum or product over a pointer or an array is not supported, " +
        "because an axiom may not read a location"
    )
  }

}

case object SimplifyFolds extends RewriterBuilder {
  override def key: String = "simplifyFolds"
  override def desc: String =
    "Replace summations and products by folds over their index range"
}

private sealed trait FoldKind[G <: Generation] {
  def label: String
  def combine(a: Expr[G], b: Expr[G])(implicit o: Origin): Expr[G]
  def identity(t: Type[G])(implicit o: Origin): Expr[G]
}

private case class SumFold[G <: Generation]() extends FoldKind[G] {
  override def label: String = "sum"
  override def combine(a: Expr[G], b: Expr[G])(implicit o: Origin): Expr[G] = a + b
  override def identity(t: Type[G])(implicit o: Origin): Expr[G] =
    t match {
      case _: IntType[G] => const[G](0)
      case t: FloatType[G] => FloatValue[G](BigDecimal(0), t)(o)
      case t => throw SimplifyFoldsErrors.CannotFoldOverType(o, t)
    }
}

private case class ProdFold[G <: Generation]() extends FoldKind[G] {
  override def label: String = "prod"
  override def combine(a: Expr[G], b: Expr[G])(implicit o: Origin): Expr[G] = a * b
  override def identity(t: Type[G])(implicit o: Origin): Expr[G] =
    t match {
      case _: IntType[G] => const[G](1)
      case t: FloatType[G] => FloatValue[G](BigDecimal(1), t)(o)
      case t => throw SimplifyFoldsErrors.CannotFoldOverType(o, t)
    }
}

case class SimplifyFolds[Pre <: Generation]() extends Rewriter[Pre] {

  private val canonicalBound =
    new Variable[Pre](TInt[Pre]())(Origin(
      Seq(PreferredName(Seq("sum_canon")))
    ))

  private def foldOrigin(label: String, preferredName: String): Origin =
    Origin(Seq(PreferredName(Seq(preferredName)), LabelContext(label)))

  private case class FoldAdt(
      adtRef: LazyRef[Post, AxiomaticDataType[Post]],
      acc: ADTFunction[Post],
  )

  private val foldAdts: mutable.Map[(FoldKind[Post], Expr[_], Seq[Type[_]]), FoldAdt] =
    mutable.Map()

  private def collectFreeVars(
      e: Expr[Pre],
      boundVar: Variable[Pre],
      preScope: CheckContext[Pre],
  ): Seq[Variable[Pre]] = {
    val scope = CheckContext[Pre](scopes = preScope.withScope(Seq(boundVar)))
    val locals = FreeVariables.freeVariablesInOrder(e, scope).flatMap {
      case FreeVariables.ReadFreeVar(Local(Ref(v))) =>
        Some(v.asInstanceOf[Variable[Pre]])
      case FreeVariables.ReadFreeVar(l) =>
        Some(l.ref.decl.asInstanceOf[Variable[Pre]])
      case _ => None
    }
    locals.toSeq.distinct
  }

  private val canonicalFreeVars: mutable.Map[Int, Variable[Pre]] = mutable.Map()

  private def canonicalFree(i: Int): Variable[Pre] =
    canonicalFreeVars.getOrElseUpdate(
      i,
      new Variable[Pre](TInt[Pre]())(Origin(
        Seq(PreferredName(Seq(s"sum_canon_fv$i")))
      )),
    )

  private def foldKey(
      kind: FoldKind[Post],
      body: Expr[Pre],
      bound: Variable[Pre],
      freeVars: Seq[Variable[Pre]],
  )(implicit o: Origin): (FoldKind[Post], Expr[_], Seq[Type[_]]) = {
    val subs: Map[Expr[Pre], Expr[Pre]] = Map(
      (Local[Pre](bound.ref): Expr[Pre]) ->
        (Local[Pre](canonicalBound.ref): Expr[Pre])
    ) ++ freeVars.zipWithIndex.map { case (v, i) =>
      (Local[Pre](v.ref): Expr[Pre]) ->
        (Local[Pre](canonicalFree(i).ref): Expr[Pre])
    }
    val canBody = new Substitute[Pre](subs).dispatch(body)
    (kind, canBody, freeVars.map(v => v.t))
  }

  private def readsLocation(e: Node[_]): Boolean = e match {
    case _: DerefPointer[_] | _: PointerSubscript[_] | _: ArraySubscript[_] => true
    case _ => e.subnodes.exists(readsLocation)
  }

  private def getFoldAdt(
      kind: FoldKind[Post],
      summandBody: Expr[Pre],
      bound: Variable[Pre],
      freeVars: Seq[Variable[Pre]],
  )(implicit o: Origin): FoldAdt = {
    val key = foldKey(kind, summandBody, bound, freeVars)
    foldAdts.get(key) match {
      case Some(adt) => adt
      case None =>
        val label = kind.label
        val indexVar = new Variable[Post](TInt())(o.where(name = s"${label}_idx"))
        val upperVar = new Variable[Post](TInt())(o.where(name = s"${label}_upper"))
        val fvVars = freeVars.zipWithIndex.map { case (v, i) =>
          new Variable[Post](v.t.asInstanceOf[Type[Post]])(
            o.where(name = s"${label}_fv$i")
          )
        }
        val allVars = indexVar +: upperVar +: fvVars

        val resultType = dispatch(summandBody).t.asInstanceOf[Type[Post]]
        val identity = kind.identity(resultType)
        val acc = new ADTFunction[Post](allVars, resultType)

        var adt: AxiomaticDataType[Post] = null
        val adtRef = new LazyRef[Post, AxiomaticDataType[Post]](adt)

        val axIndexVar =
          new Variable[Post](TInt())(o.where(name = s"${label}_axidx"))
        val axUpper =
          new Variable[Post](TInt())(o.where(name = s"${label}_axupper"))
        val axFvVars = freeVars.zipWithIndex.map { case (v, i) =>
          new Variable[Post](v.t.asInstanceOf[Type[Post]])(
            o.where(name = s"${label}_axfv$i")
          )
        }
        val axVars = axIndexVar +: axUpper +: axFvVars.toSeq

        val axIndexLocal = Local[Post](axIndexVar.ref)
        val axUpperLocal = Local[Post](axUpper.ref)
        val axFvLocals = axFvVars.map(v => Local[Post](v.ref))

        def accAppFvs(ix: Expr[Post]): Expr[Post] =
          ADTFunctionInvocation[Post](
            Some((adtRef, Nil)),
            acc.ref,
            ix +: axUpperLocal +: axFvLocals,
          )

        val baseAxiom =
          new ADTAxiom(Forall[Post](
            axVars,
            Seq(Seq(accAppFvs(axIndexLocal))),
            (axIndexLocal >= axUpperLocal) ==>
              (accAppFvs(axIndexLocal) === identity),
          ))

        val bodyPost = dispatch(summandBody)
        if (readsLocation(bodyPost)) {
          throw SimplifyFoldsErrors.CannotFoldOverLocation(o)
        }
        val subs: Map[Expr[Post], Expr[Post]] =
          freeVars.map(v => (Local[Post](succ(v)): Expr[Post]))
            .zip(axFvLocals).toMap +
            ((Local[Post](succ(bound)): Expr[Post]) ->
              (axIndexLocal: Expr[Post]))

        val summand = new Substitute[Post](subs).dispatch(bodyPost)
        val next = accAppFvs(axIndexLocal + const[Post](1))

        val stepAxiom =
          new ADTAxiom(Forall[Post](
            axVars,
            Seq(Seq(accAppFvs(axIndexLocal))),
            (axIndexLocal < axUpperLocal) ==>
              (accAppFvs(axIndexLocal) === kind.combine(summand, next)),
          ))

        adt =
          new AxiomaticDataType[Post](Seq(acc, baseAxiom, stepAxiom), Nil)(
            foldOrigin(label, label)
          )
        globalDeclarations.declare(adt)

        val entry = FoldAdt(adtRef = adtRef, acc = acc)
        foldAdts(key) = entry
        entry
    }
  }

  override def dispatch(e: Expr[Pre]): Expr[Rewritten[Pre]] =
    e match {
      case sum @ Sum(binding, lo, hi, body) =>
        dispatchFold(SumFold[Post](), binding, lo, hi, body)(sum.o)
      case prod @ Product(binding, lo, hi, body) =>
        dispatchFold(ProdFold[Post](), binding, lo, hi, body)(prod.o)
      case other => other.rewriteDefault()
    }

  private def dispatchFold(
      kind: FoldKind[Post],
      binding: Variable[Pre],
      lo: Expr[Pre],
      hi: Expr[Pre],
      body: Expr[Pre],
  )(implicit o: Origin): Expr[Rewritten[Pre]] =
    variables.scope {
      variables.dispatch(binding)
      val preScope = CheckContext[Pre](scopes =
        CheckContext[Pre]().withScope(Seq(binding))
      )
      val freeVars = collectFreeVars(body, binding, preScope)
      val adt = getFoldAdt(kind, body, binding, freeVars)
      val lower = dispatch(lo)
      val upper = dispatch(hi)
      val argVars = freeVars.map(v => Local[Post](succ(v)))
      ADTFunctionInvocation[Post](
        Some((adt.adtRef, Nil)),
        adt.acc.ref,
        lower +: upper +: argVars,
      )
    }
}