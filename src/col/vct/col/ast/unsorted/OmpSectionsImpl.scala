package vct.col.ast.unsorted

import vct.col.ast.OmpSections
import vct.col.ast.ops.OmpSectionsOps
import vct.col.print._

trait OmpSectionsImpl[G] extends OmpSectionsOps[G] { this: OmpSections[G] =>
  // override def layout(implicit ctx: Ctx): Doc = ???
}
