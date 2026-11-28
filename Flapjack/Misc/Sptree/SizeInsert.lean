module

public import Flapjack.Misc.Sptree

@[expose] public section

/-!
# Size of an insertion in the sparse tree

Counterpart of `size_insert` from `HOL/src/finite_maps/sptreeScript.sml`:
inserting a binding grows the size by one exactly when the key is not already
in the domain.
-/

namespace Flapjack

private theorem sptInsert_ln {α : Type} (key : Nat) (value : α) :
    sptInsert key value (.ln : Spt α) =
      if key = 0 then .ls value
      else if key % 2 = 0 then .bn (sptInsert ((key - 1) / 2) value .ln) .ln
      else .bn .ln (sptInsert ((key - 1) / 2) value .ln) := by
  rw [sptInsert.eq_1]

private theorem sptInsert_ls {α : Type} (key : Nat) (value existing : α) :
    sptInsert key value (.ls existing : Spt α) =
      if key = 0 then .ls value
      else if key % 2 = 0 then .bs (sptInsert ((key - 1) / 2) value .ln) existing .ln
      else .bs .ln existing (sptInsert ((key - 1) / 2) value .ln) := by
  rw [sptInsert.eq_2]

private theorem sptInsert_bn {α : Type} (key : Nat) (value : α) (left right : Spt α) :
    sptInsert key value (.bn left right) =
      if key = 0 then .bs left value right
      else if key % 2 = 0 then .bn (sptInsert ((key - 1) / 2) value left) right
      else .bn left (sptInsert ((key - 1) / 2) value right) := by
  rw [sptInsert.eq_3]

private theorem sptInsert_bs {α : Type} (key : Nat) (value existing : α)
    (left right : Spt α) :
    sptInsert key value (.bs left existing right) =
      if key = 0 then .bs left value right
      else if key % 2 = 0 then .bs (sptInsert ((key - 1) / 2) value left) existing right
      else .bs left existing (sptInsert ((key - 1) / 2) value right) := by
  rw [sptInsert.eq_4]

open Classical in
/-- Original `size_insert`. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "size_insert"]
theorem sptSize_sptInsert {α : Type} :
    ∀ (key : Nat) (value : α) (tree : Spt α),
      sptSize (sptInsert key value tree) =
        if sptDomain tree key then sptSize tree else sptSize tree + 1 := by
  intro key
  induction key using Nat.strongRecOn with
  | ind key ih =>
    intro value tree
    cases tree with
    | ln =>
      by_cases hzero : key = 0
      · rw [sptInsert_ln, if_pos hzero]
        simp [sptLookup, sptDomain]
      · have hsub := ih ((key - 1) / 2) (by omega) value (.ln : Spt α)
        by_cases hparity : key % 2 = 0
        · rw [sptInsert_ln, if_neg hzero, if_pos hparity]
          simp [sptLookup, sptDomain, hsub]
        · rw [sptInsert_ln, if_neg hzero, if_neg hparity]
          simp [sptLookup, sptDomain, hsub]
    | ls existing =>
      by_cases hzero : key = 0
      · rw [sptInsert_ls, if_pos hzero]
        simp [sptLookup, sptDomain, hzero]
      · have hsub := ih ((key - 1) / 2) (by omega) value (.ln : Spt α)
        by_cases hparity : key % 2 = 0
        · rw [sptInsert_ls, if_neg hzero, if_pos hparity]
          simp [sptLookup, sptDomain, hzero, hsub]
        · rw [sptInsert_ls, if_neg hzero, if_neg hparity]
          simp [sptLookup, sptDomain, hzero, hsub]
    | bn left right =>
      by_cases hzero : key = 0
      · rw [sptInsert_bn, if_pos hzero]
        simp [sptLookup, sptDomain, hzero]
      · by_cases hparity : key % 2 = 0
        · have hsub := ih ((key - 1) / 2) (by omega) value left
          rw [sptInsert_bn, if_neg hzero, if_pos hparity]
          by_cases hdom : (sptLookup ((key - 1) / 2) left).isSome
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
            omega
        · have hsub := ih ((key - 1) / 2) (by omega) value right
          rw [sptInsert_bn, if_neg hzero, if_neg hparity]
          by_cases hdom : (sptLookup ((key - 1) / 2) right).isSome
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
            omega
    | bs left existing right =>
      by_cases hzero : key = 0
      · rw [sptInsert_bs, if_pos hzero]
        simp [sptLookup, sptDomain, hzero]
      · by_cases hparity : key % 2 = 0
        · have hsub := ih ((key - 1) / 2) (by omega) value left
          rw [sptInsert_bs, if_neg hzero, if_pos hparity]
          by_cases hdom : (sptLookup ((key - 1) / 2) left).isSome
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
            omega
        · have hsub := ih ((key - 1) / 2) (by omega) value right
          rw [sptInsert_bs, if_neg hzero, if_neg hparity]
          by_cases hdom : (sptLookup ((key - 1) / 2) right).isSome
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
          · simp [sptLookup, sptDomain, hzero, hparity, hsub, hdom]
            omega

end Flapjack
