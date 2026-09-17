package vct.col.ast.unsorted

import vct.col.ast.OmpSection
import vct.col.ast.ops.OmpSectionOps
import vct.col.print._

trait OmpSectionImpl[G] extends OmpSectionOps[G] { this: OmpSection[G] =>
  // override def layout(implicit ctx: Ctx): Doc = ???
}
