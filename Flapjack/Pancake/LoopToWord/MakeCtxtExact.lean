module

public import Flapjack.HolRef
public import Flapjack.Misc.Sptree

@[expose] public section

/-!
# Exact `make_ctxt_def` port

HOL `make_ctxt` (`cakeml/pancake/loop_to_wordScript.sml:152-155`) folds a list
of variable names into an `sptree` context mapping each name to the even
register `next, next + 2, ...`.  The HOL context is `num |-> num`, rendered
constructor-for-constructor by `Spt Nat`, and the insertion is the reviewed
`sptInsert`.

The executed `comp_func` chain uses this exact rendering:
`panToWordCompileProgHOL` → `loopToWordCompileHOL` →
`loopToWordCompileProgHOL` → `loopToWordCompFuncHOL` calls `makeCtxtHOL`
directly.
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
