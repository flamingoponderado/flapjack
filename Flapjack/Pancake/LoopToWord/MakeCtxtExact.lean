import Flapjack.HolRef
import Flapjack.Misc.Sptree

/-!
# Exact `make_ctxt_def` port

HOL `make_ctxt` (`cakeml/pancake/loop_to_wordScript.sml:152-155`) folds a list
of variable names into an `sptree` context mapping each name to the even
register `next, next + 2, ...`.  The HOL context is `num |-> num`, rendered
constructor-for-constructor by `Spt Nat`, and the insertion is the reviewed
`sptInsert`.

The production compiler keeps its own association-list `makeCtxt`
(`Flapjack/Pancake/LoopToWord.lean:50`), whose observable `find_var` behaviour
is tracked separately.  This exact rendering is the reviewed counterpart of
the HOL definition used by the `comp_func` chain, so the executable route is
still tracked by the `comp_func` prerequisite beads rather than claimed here.
-/

namespace Flapjack

/-- Exact HOL `make_ctxt_def`
(`cakeml/pancake/loop_to_wordScript.sml:152-155`).  Starting from `next`, each
variable in turn receives the next even register in the context. -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "make_ctxt_def"]
def makeCtxtHOL : Nat → List Nat → Spt Nat → Spt Nat
  | _, [], context => context
  | next, name :: rest, context =>
      makeCtxtHOL (next + 2) rest (sptInsert name next context)

end Flapjack
