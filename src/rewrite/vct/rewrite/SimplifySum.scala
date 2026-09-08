package vct.col.rewrite

import vct.col.ast._
import vct.col.{ast => col}
import vct.col.origin.{LabelContext, Origin, PreferredName}
import vct.col.ref.{LazyRef, Ref}
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder, Rewritten}
import vct.col.util.AstBuildHelpers._
import vct.col.util.Substitute

import scala.collection.mutable

case object SimplifySum extends RewriterBuilder {
  override def key: String = "simplifySums"
  override def desc: String = "Replace summations with provable functions"

  case class NotImplementedSum(sum: col.Sum[_])
      extends vct.result.VerificationError.SystemError {
    override def text: String =
      "This sum expression cannot be reduced, since it is not of the form " +
        "(\\sum x; lo <= x && x < hi; body) with a single integer bound variable."
  }
}

case class SimplifySum[Pre <: Generation]() extends Rewriter[Pre] {
  import SimplifySum.NotImplementedSum

  private val canonicalBound = new col.Variable[Pre](TInt[Pre]())(
    Origin(Seq(PreferredName(Seq("sum_canon"))))
  )

  private def SumOrigin(preferredName: String): Origin =
    Origin(Seq(PreferredName(Seq(preferredName)), LabelContext("sum")))

  private case class SumAdt(
      adtRef: LazyRef[Post, col.AxiomaticDataType[Post]],
      acc: col.ADTFunction[Post],
  )

  private val sumAdts: mutable.Map[(col.Expr[_], Seq[col.Type[_]]), SumAdt] =
    mutable.Map()

  private def extractBoundedRange(
      boundVar: col.Variable[Pre],
      condition: col.Expr[Pre],
  ): Option[(col.Expr[Pre], col.Expr[Pre], Boolean)] = {
    condition match {
      case col.SetMember(other, r @ col.RangeSet(lo, hi)) if isBound(other) =>
        return Some((lo, hi, false))
      case _ =>
    }

    def isBound(e: col.Expr[Pre]): Boolean = e match {
      case col.Local(Ref(v)) => v eq boundVar
      case _ => false
    }

    def conjuncts(e: col.Expr[Pre]): Seq[col.Expr[Pre]] = e match {
      case col.And(l, r) => conjuncts(l) ++ conjuncts(r)
      case other => Seq(other)
    }

    val conjs = conjuncts(condition)

    val lo = conjs.collectFirst {
      case col.LessEq(l, r) if isBound(r) => l
      case col.Less(l, r) if isBound(r) => l
    }

    val hi = conjs.collectFirst {
      case col.LessEq(l, r) if isBound(l) => (r, true)
      case col.Less(l, r) if isBound(l) => (r, false)
    }

    for {
      l <- lo
      (h, incl) <- hi
    } yield (l, h, incl)
  }

  private def collectFreeVars(
      e: col.Expr[Pre],
      boundVar: col.Variable[Pre],
  ): Seq[col.Variable[Pre]] = {
    val vars = mutable.LinkedHashSet.empty[col.Variable[Pre]]
    e.foreach {
      case col.Local(Ref(v)) if !(v eq boundVar) => vars += v
      case _ =>
    }
    vars.toSeq
  }

  private def sumKey(
      body: col.Expr[Pre],
      bound: col.Variable[Pre],
      freeVars: Seq[col.Variable[Pre]],
  )(implicit o: Origin): (col.Expr[_], Seq[col.Type[_]]) = {
    val subs: Map[col.Expr[Pre], col.Expr[Pre]] =
      Map((Local[Pre](bound.ref): col.Expr[Pre]) ->
        (Local[Pre](canonicalBound.ref): col.Expr[Pre]))
    val canBody = new Substitute[Pre](subs).dispatch(body)
    (canBody, freeVars.map(v => v.t))
  }

  private def getSumAdt(
      hi: col.Expr[Pre],
      body: col.Expr[Pre],
      bound: col.Variable[Pre],
      freeVars: Seq[col.Variable[Pre]],
  )(implicit o: Origin): SumAdt = {
    val key = sumKey(body, bound, freeVars)
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

        val acc = new col.ADTFunction[Post](allVars, TInt())

        var adt: col.AxiomaticDataType[Post] = null
        val adtRef = new LazyRef[Post, col.AxiomaticDataType[Post]](adt)

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
          col.ADTFunctionInvocation[Post](
            Some((adtRef, Nil)),
            acc.ref,
            ix +: axUpperLocal +: axFvLocals,
          )

        val baseAxiom = new col.ADTAxiom(
          Forall[Post](
            axVars,
            Seq(Seq(accAppFvs(axIndexLocal))),
            (axIndexLocal >= axUpperLocal) ==> (accAppFvs(axIndexLocal) === const[Post](0)),
          )
        )

        val bodyPost = dispatch(body)
        val subs: Map[col.Expr[Post], col.Expr[Post]] =
          freeVars.map(v => (Local[Post](succ(v)): col.Expr[Post])).zip(
            axFvLocals
          ).toMap +
            ((Local[Post](succ(bound)): col.Expr[Post]) -> (axIndexLocal: col.Expr[Post]))

        val summand = new Substitute[Post](subs).dispatch(bodyPost)
        val next = accAppFvs(axIndexLocal + const[Post](1))

        val stepAxiom = new col.ADTAxiom(
          Forall[Post](
            axVars,
            Seq(Seq(accAppFvs(axIndexLocal))),
            (axIndexLocal < axUpperLocal) ==> (accAppFvs(axIndexLocal) === (summand + next)),
          )
        )

        adt = new col.AxiomaticDataType[Post](Seq(acc, baseAxiom, stepAxiom), Nil)(
          SumOrigin("sum")
        )
        globalDeclarations.declare(adt)

        val entry = SumAdt(
          adtRef = adtRef,
          acc = acc,
        )
        sumAdts(key) = entry
        entry
    }
  }

  override def dispatch(e: col.Expr[Pre]): col.Expr[Rewritten[Pre]] =
    e match {
      case sum @ col.Sum(Seq(bound), _, range, body) =>
        implicit val o: Origin = sum.o
        val boundPre = bound
        variables.scope {
          variables.dispatch(boundPre)
          extractBoundedRange(boundPre, range) match {
            case None => throw NotImplementedSum(sum)
            case Some((lo, hi, hiInclusive)) =>
              val freeVars = collectFreeVars(body, boundPre)
              val adt = getSumAdt(hi, body, boundPre, freeVars)
              val finalLo: Expr[Post] = dispatch(lo)
              val finalHi: Expr[Post] =
                if (hiInclusive) dispatch(hi) + const[Post](1) else dispatch(hi)
              col.ADTFunctionInvocation[Post](
                Some((adt.adtRef, Nil)),
                adt.acc.ref,
                finalLo +: finalHi +: freeVars.map(v => Local[Post](succ(v))),
              )
          }
        }
      case other => other.rewriteDefault()
    }
}