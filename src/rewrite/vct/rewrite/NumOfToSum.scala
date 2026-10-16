package vct.rewrite

import vct.col.ast._
import vct.col.origin.Origin
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder, Rewritten}
import vct.col.util.AstBuildHelpers._

case object NumOfToSum extends RewriterBuilder {
  override def key: String = "numOfToSum"
  override def desc: String =
    "Replaces each numof by a sum counting the iterations in which the body holds"
}

case class NumOfToSum[Pre <: Generation]() extends Rewriter[Pre] {
  override def dispatch(e: Expr[Pre]): Expr[Rewritten[Pre]] =
    e match {
      case numof @ NumOf(binding, lo, hi, body) =>
        implicit val o: Origin = numof.o
        variables.scope {
          Sum(
            variables.dispatch(binding),
            dispatch(lo),
            dispatch(hi),
            Select(dispatch(body), const(1), const(0)),
          )
        }
      case other => other.rewriteDefault()
    }
}