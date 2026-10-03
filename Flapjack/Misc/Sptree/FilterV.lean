import Flapjack.Misc.Sptree

namespace Flapjack

/-- Exact HOL `sptree$filter_v` (`sptreeScript.sml:1808-1815`, pinned HOL submodule):
keep the values satisfying `f`, with the `mk_BN`/`mk_BS` collapsing; all four
clauses are literal. HOL's `bool` predicate is a Lean `Bool` function. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "filter_v_def"]
def sptFilterV {α : Type} (f : α → Bool) : Spt α → Spt α
  | .ln => .ln
  | .ls x => if f x then .ls x else .ln
  | .bn l r => sptMkBN (sptFilterV f l) (sptFilterV f r)
  | .bs l x r =>
      if f x then sptMkBS (sptFilterV f l) x (sptFilterV f r)
      else sptMkBN (sptFilterV f l) (sptFilterV f r)

end Flapjack
