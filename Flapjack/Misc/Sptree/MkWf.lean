module

public import Flapjack.Misc.Sptree

@[expose] public section

/-! Canonicalize the structure of a sparse tree. -/
namespace Flapjack

/-- Recursively remove redundant empty branches using HOL's smart constructors. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "mk_wf_def"]
def sptMkWf {α : Type} : Spt α → Spt α
  | .ln => .ln
  | .ls value => .ls value
  | .bn left right => sptMkBN (sptMkWf left) (sptMkWf right)
  | .bs left value right => sptMkBS (sptMkWf left) value (sptMkWf right)

private theorem lookup_mkBN {α : Type} (left right : Spt α) (key : Nat) :
    sptLookup key (sptMkBN left right) = sptLookup key (.bn left right) := by
  cases left <;> cases right <;> by_cases h0 : key = 0 <;>
    by_cases he : key % 2 = 0 <;> simp [sptMkBN, sptLookup, h0, he]

private theorem lookup_mkBS {α : Type} (left : Spt α) (value : α) (right : Spt α) (key : Nat) :
    sptLookup key (sptMkBS left value right) = sptLookup key (.bs left value right) := by
  cases left <;> cases right <;> by_cases h0 : key = 0 <;>
    by_cases he : key % 2 = 0 <;> simp [sptMkBS, sptLookup, h0, he]

/-- Normalizing a sparse tree preserves every lookup, including on malformed
trees and keys absent from the original tree. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "lookup_mk_wf"]
theorem sptLookup_mkWf {α : Type} (key : Nat) (tree : Spt α) :
    sptLookup key (sptMkWf tree) = sptLookup key tree := by
  induction tree generalizing key with
  | ln => rfl
  | ls value => rfl
  | bn left right ihLeft ihRight =>
    simp only [sptMkWf, lookup_mkBN, sptLookup]
    split <;> try rfl
    split <;> simp_all
  | bs left value right ihLeft ihRight =>
    simp only [sptMkWf, lookup_mkBS, sptLookup]
    split <;> try rfl
    split <;> simp_all

end Flapjack
