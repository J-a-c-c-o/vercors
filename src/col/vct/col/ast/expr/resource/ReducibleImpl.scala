package vct.col.ast.expr.resource

import vct.col.ast.{Reducible, TResource, Type}
import vct.col.print.{Ctx, Doc, Group, Precedence, Text}
import vct.col.ast.ops.ReducibleOps

trait ReducibleImpl[G] extends ReducibleOps[G] {
  this: Reducible[G] =>
  override def t: Type[G] = TResource()

  override def precedence: Int = Precedence.ATOMIC
  override def layout(implicit ctx: Ctx): Doc =
    Group(Text("Reducible(") <> Doc.arg(res) <> "," <+> Text(op.toString) <> ")")
}
