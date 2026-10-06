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

object SimplifySumErrors {
  case class CannotSumOverType(at: Origin, t: Type[_]) extends UserError {
    override def code: String = "sumUnsupportedType"
    override def text: String =
      at.messageInContext(s"A sum over a value of type $t is not supported")
  }

  case class CannotSumOverLocation(at: Origin) extends UserError {
    override def code: String = "sumOverLocation"
    override def text: String = at.messageInContext(
      "A sum over a pointer or an array is not supported, because an axiom " +
        "may not read a location"
    )
  }

}

case object SimplifySum extends RewriterBuilder {
  override def key: String = "simplifySums"
  override def desc: String =
    "Replace summations by folds over their index range"
}

case class SimplifySum[Pre <: Generation]() extends Rewriter[Pre] {

  private val canonicalBound =
    new Variable[Pre](TInt[Pre]())(Origin(
      Seq(PreferredName(Seq("sum_canon")))
    ))

  private def zeroOf(t: Type[Post])(implicit o: Origin): Expr[Post] = t match {
    case _: IntType[Post] => const[Post](0)
    case t: FloatType[Post] => FloatValue[Post](BigDecimal(0), t)(o)
    case t =>
      throw SimplifySumErrors.CannotSumOverType(o, t)
  }

  private def sumOrigin(preferredName: String): Origin =
    Origin(Seq(PreferredName(Seq(preferredName)), LabelContext("sum")))

  private case class SumAdt(
      adtRef: LazyRef[Post, AxiomaticDataType[Post]],
      acc: ADTFunction[Post],
  )

  private val sumAdts: mutable.Map[(Expr[_], Seq[Type[_]]), SumAdt] =
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

  private def sumKey(
      body: Expr[Pre],
      bound: Variable[Pre],
      freeVars: Seq[Variable[Pre]],
  )(implicit o: Origin): (Expr[_], Seq[Type[_]]) = {
    val subs: Map[Expr[Pre], Expr[Pre]] = Map(
      (Local[Pre](bound.ref): Expr[Pre]) ->
        (Local[Pre](canonicalBound.ref): Expr[Pre])
    ) ++ freeVars.zipWithIndex.map { case (v, i) =>
      (Local[Pre](v.ref): Expr[Pre]) ->
        (Local[Pre](canonicalFree(i).ref): Expr[Pre])
    }
    val canBody = new Substitute[Pre](subs).dispatch(body)
    (canBody, freeVars.map(v => v.t))
  }

  private def readsLocation(e: Node[_]): Boolean = e match {
    case _: DerefPointer[_] | _: PointerSubscript[_] | _: ArraySubscript[_] => true
    case _ => e.subnodes.exists(readsLocation)
  }

  private def getSumAdt(
      summandBody: Expr[Pre],
      bound: Variable[Pre],
      freeVars: Seq[Variable[Pre]],
  )(implicit o: Origin): SumAdt = {
    val key = sumKey(summandBody, bound, freeVars)
    sumAdts.get(key) match {
      case Some(adt) => adt
      case None =>
        val indexVar = new Variable[Post](TInt())(o.where(name = "sum_idx"))
        val upperVar = new Variable[Post](TInt())(o.where(name = "sum_upper"))
        val fvVars = freeVars.zipWithIndex.map { case (v, i) =>
          new Variable[Post](v.t.asInstanceOf[Type[Post]])(
            o.where(name = s"sum_fv$i")
          )
        }
        val allVars = indexVar +: upperVar +: fvVars

        val resultType = dispatch(summandBody).t.asInstanceOf[Type[Post]]
        val zero = zeroOf(resultType)
        val acc = new ADTFunction[Post](allVars, resultType)

        var adt: AxiomaticDataType[Post] = null
        val adtRef = new LazyRef[Post, AxiomaticDataType[Post]](adt)

        val axIndexVar = new Variable[Post](TInt())(o.where(name = "sum_axidx"))
        val axUpper = new Variable[Post](TInt())(o.where(name = "sum_axupper"))
        val axFvVars = freeVars.zipWithIndex.map { case (v, i) =>
          new Variable[Post](v.t.asInstanceOf[Type[Post]])(
            o.where(name = s"sum_axfv$i")
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
              (accAppFvs(axIndexLocal) === zero),
          ))

        val bodyPost = dispatch(summandBody)
        if (readsLocation(bodyPost)) {
          throw SimplifySumErrors.CannotSumOverLocation(o)
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
              (accAppFvs(axIndexLocal) === (summand + next)),
          ))

        adt =
          new AxiomaticDataType[Post](Seq(acc, baseAxiom, stepAxiom), Nil)(
            sumOrigin("sum")
          )
        globalDeclarations.declare(adt)

        val entry = SumAdt(adtRef = adtRef, acc = acc)
        sumAdts(key) = entry
        entry
    }
  }

  override def dispatch(e: Expr[Pre]): Expr[Rewritten[Pre]] =
    e match {
      case sum @ Sum(binding, lo, hi, body) =>
        implicit val o: Origin = sum.o
        variables.scope {
          variables.dispatch(binding)
          val preScope = CheckContext[Pre](scopes =
            CheckContext[Pre]().withScope(Seq(binding))
          )
          val freeVars = collectFreeVars(body, binding, preScope)
          val adt = getSumAdt(body, binding, freeVars)
          val lower = dispatch(lo)
          val upper = dispatch(hi)
          val argVars = freeVars.map(v => Local[Post](succ(v)))
          val invocation = ADTFunctionInvocation[Post](
            Some((adt.adtRef, Nil)),
            adt.acc.ref,
            lower +: upper +: argVars,
          )

          invocation
        }
      case other => other.rewriteDefault()
    }
}