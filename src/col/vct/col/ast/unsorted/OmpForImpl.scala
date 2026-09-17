package vct.col.ast.unsorted

import vct.col.ast.OmpFor
import vct.col.ast.ops.OmpForOps
import vct.col.print._

trait OmpForImpl[G] extends OmpForOps[G] { this: OmpFor[G] =>
  // override def layout(implicit ctx: Ctx): Doc = ???
}
