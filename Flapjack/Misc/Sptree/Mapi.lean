import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal indexed Spt traversal. The root receives the current index;
the left and right children receive respectively twice and once `lrNext`.
The source smart constructors normalize even malformed input trees.
This definition does not require well-formedness or restrict either payload. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "mapi0_def"]
def sptMapi0 {α β : Type} (f : Nat → α → β) (index : Nat) : Spt α → Spt β
  | .ln => .ln
  | .ls value => .ls (f index value)
  | .bn left right =>
      let inc := lrNext index
      sptMkBN (sptMapi0 f (index + 2 * inc) left)
        (sptMapi0 f (index + inc) right)
  | .bs left value right =>
      let inc := lrNext index
      sptMkBS (sptMapi0 f (index + 2 * inc) left) (f index value)
        (sptMapi0 f (index + inc) right)

/-- Literal indexed map starting at source index zero. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "mapi_def"]
def sptMapi {α β : Type} (f : Nat → α → β) (tree : Spt α) : Spt β :=
  sptMapi0 f 0 tree

end Flapjack
