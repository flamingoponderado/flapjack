import Flapjack.Misc.Sptree
import Flapjack.Misc.Sptree.Wf

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

/-- Exact HOL `lookup_filter_v` (`sptreeScript.sml:1817-1824`, pinned HOL submodule). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "lookup_filter_v"]
theorem sptLookupFilterV {α : Type} :
    ∀ (k : Nat) (t : Spt α) (f : α → Bool),
      sptLookup k (sptFilterV f t) =
        match sptLookup k t with
        | some v => if f v then some v else none
        | none => none := by
  intro k t f
  induction t generalizing k with
  | ln => simp [sptFilterV, sptLookup]
  | ls x =>
      by_cases hk : k = 0 <;> by_cases hf : f x = true <;> simp [sptFilterV, sptLookup, hk, hf]
  | bn l r ihl ihr =>
      simp only [sptFilterV, sptLookupMkBN]
      by_cases hk : k = 0
      · simp [sptLookup, hk]
      · simp only [sptLookup, hk, if_false]
        split
        · exact ihl _
        · exact ihr _
  | bs l x r ihl ihr =>
      by_cases hf : f x = true
      · simp only [sptFilterV, hf, if_true, sptLookupMkBS]
        by_cases hk : k = 0
        · simp [sptLookup, hk, hf]
        · simp only [sptLookup, hk, if_false]
          split
          · exact ihl _
          · exact ihr _
      · simp only [sptFilterV, hf, Bool.false_eq_true, if_false, sptLookupMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk, hf]
        · simp only [sptLookup, hk, if_false]
          split
          · exact ihl _
          · exact ihr _

end Flapjack
