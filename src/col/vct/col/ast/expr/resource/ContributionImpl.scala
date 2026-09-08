package vct.col.ast.expr.resource

import vct.col.ast.{Contribution, TResource, Type}
import vct.col.print.{Ctx, Doc, Group, Precedence, Text}
import vct.col.ast.ops.ContributionOps

trait ContributionImpl[G] extends ContributionOps[G] {
  this: Contribution[G] =>
  override def t: Type[G] = TResource()

  override def precedence: Int = Precedence.ATOMIC
  override def layout(implicit ctx: Ctx): Doc =
    Group(Text("Contribution(") <> Doc.arg(res) <> "," <+> Doc.arg(value) <> ")")
}
