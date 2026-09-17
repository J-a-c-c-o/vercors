package vct.col.ast.unsorted

import vct.col.ast.OmpParallel
import vct.col.ast.ops.OmpParallelOps
import vct.col.print._

trait OmpParallelImpl[G] extends OmpParallelOps[G] { this: OmpParallel[G] =>
  // override def layout(implicit ctx: Ctx): Doc = ???
}
