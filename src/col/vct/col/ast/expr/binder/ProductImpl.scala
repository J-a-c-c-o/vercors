package vct.col.ast.expr.binder

import vct.col.ast.ops.ProductOps
import vct.col.ast.{Product, Type, Variable}
import vct.col.print._

trait ProductImpl[G] extends ProductOps[G] {
  this: Product[G] =>
  override def t: Type[G] = body.t

  override def bindings: Seq[Variable[G]] = Seq(binding)

  def layoutSpec(implicit ctx: Ctx): Doc =
    Group(
      Text("(\\prod") <+> binding <+> Text("\\in") <+> Text("{") <> lo <+>
        Text("..") <+> hi <> Text("};") <+> body <> ")"
    )

  def layoutSilver(implicit ctx: Ctx): Doc =
    Group(
      Text("(prod") <+> binding <+> "::" <+> lo <> "," <+> hi <+> "::" <+> body <>
        ")"
    )

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc =
    ctx.syntax match {
      case Ctx.Silver => layoutSilver
      case _ => layoutSpec
    }
}
