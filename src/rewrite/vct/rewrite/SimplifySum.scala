package vct.col.rewrite

import vct.col.ast._
import vct.col.origin.{LabelContext, Origin, PreferredName}
import vct.col.ref.{LazyRef, Ref}
import vct.col.rewrite.util.FreeVariables
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder, Rewritten}
import vct.col.check.CheckContext
import vct.col.util.AstBuildHelpers._
import vct.col.util.Substitute

import scala.collection.mutable

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

  private def SumOrigin(preferredName: String): Origin =
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
    val locals = FreeVariables.freeVariables(e, scope).flatMap {
      case FreeVariables.ReadFreeVar(Local(Ref(v))) =>
        Some(v.asInstanceOf[Variable[Pre]])
      case FreeVariables.ReadFreeVar(l) =>
        Some(l.ref.decl.asInstanceOf[Variable[Pre]])
      case _ => None
    }
    locals.toSeq.distinct
  }

  private def sumKey(
      body: Expr[Pre],
      bound: Variable[Pre],
      freeVars: Seq[Variable[Pre]],
  )(implicit o: Origin): (Expr[_], Seq[Type[_]]) = {
    val subs: Map[Expr[Pre], Expr[Pre]] = Map(
      (Local[Pre](bound.ref): Expr[Pre]) ->
        (Local[Pre](canonicalBound.ref): Expr[Pre])
    )
    val canBody = new Substitute[Pre](subs).dispatch(body)
    (canBody, freeVars.map(v => v.t))
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

        val acc = new ADTFunction[Post](allVars, TInt())

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
              (accAppFvs(axIndexLocal) === const[Post](0)),
          ))

        val bodyPost = dispatch(summandBody)
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
            SumOrigin("sum")
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
          ADTFunctionInvocation[Post](
            Some((adt.adtRef, Nil)),
            adt.acc.ref,
            dispatch(lo) +: dispatch(hi) +: freeVars.map(v => Local[Post](succ(v))),
          )
        }
      case other => other.rewriteDefault()
    }
}