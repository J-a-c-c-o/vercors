package vct.col.ast.expr.binder

import vct.col.ast.{Sum, TInt, Type}
import vct.col.ast.ops.SumOps
import vct.col.print._

trait SumImpl[G] extends SumOps[G] {
  this: Sum[G] =>
  override def t: Type[G] = TInt()

  def layoutSpec(implicit ctx: Ctx): Doc =
    Group(
      Text("(\\sum") <+> Doc.fold(bindings)(_ <> "," <+> _) <> ";" <>>
        range <> ";" <+> body </> ")"
    )

  def layoutSilver(implicit ctx: Ctx): Doc =
    Group(
      Text("(sum") <+> Doc.fold(bindings)(_ <> "," <+> _) <+> "::" <>
        range <+> "::" <+> body </> ")"
    )

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc =
    ctx.syntax match {
      case Ctx.Silver => layoutSilver
      case _ => layoutSpec
    }
}
