import Flapjack.Misc.Sptree

/-! Canonicalize the structure of a sparse tree. -/
namespace Flapjack

/-- Recursively remove redundant empty branches using HOL's smart constructors. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "mk_wf_def"]
def sptMkWf {α : Type} : Spt α → Spt α
  | .ln => .ln
  | .ls value => .ls value
  | .bn left right => sptMkBN (sptMkWf left) (sptMkWf right)
  | .bs left value right => sptMkBS (sptMkWf left) value (sptMkWf right)

end Flapjack
