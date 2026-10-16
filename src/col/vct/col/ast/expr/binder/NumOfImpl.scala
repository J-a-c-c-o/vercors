package vct.col.ast.expr.binder

import vct.col.ast.{NumOf, TInt, Type, Variable}
import vct.col.ast.ops.NumOfOps
import vct.col.print._

trait NumOfImpl[G] extends NumOfOps[G] {
  this: NumOf[G] =>

  override def t: Type[G] = TInt[G]()

  override def bindings: Seq[Variable[G]] = Seq(binding)

  def layoutSpec(implicit ctx: Ctx): Doc =
    Group(
      Text("(\\numof") <+> binding <+> Text("\\in") <+> Text("{") <> lo <+>
        Text("..") <+> hi <> Text("};") <+> body <> ")"
    )

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc = layoutSpec
}