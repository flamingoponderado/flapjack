module

public import Flapjack.Compiler.Backend.ClosToBvl.Sort
public import Mathlib.Data.List.Permutation
public import Flapjack.Misc.Sptree.Wf
import Mathlib.Data.List.Nodup

@[expose] public section

namespace Flapjack.Compiler.Backend.ClosToBvl

@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_split_IMP_PERM"]
theorem codeSplit_imp_perm {α : Type} (xs1 xs2 xs3 ts1 ts2 : List α)
    (split : codeSplit xs1 xs2 xs3 = (ts1, ts2)) :
    (ts1 ++ ts2).Perm (xs2 ++ xs3 ++ xs1) := by
  classical
  rw [List.perm_iff_count]
  intro value
  induction xs1 generalizing xs2 xs3 with
  | nil =>
    simp [codeSplit] at split
    rcases split with ⟨rfl, rfl⟩
    simp
  | cons head tail ih =>
    have h := ih (head :: xs3) xs2 (by simpa [codeSplit] using split)
    simp only [List.count_append, List.count_cons] at h ⊢
    omega

/-- Merge preserves any permutation of its two inputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "IMP_PERM_code_merge"]
theorem codeMerge_imp_perm {α : Type} (xs ys zs : List (Nat × α))
    (h : (xs ++ ys).Perm zs) : (codeMerge xs ys).Perm zs := by
  fun_induction codeMerge xs ys generalizing zs with
  | case1 ys => simpa [codeMerge] using h
  | case2 xs ne => simpa [codeMerge] using h
  | case3 x xs y ys _ ih =>
    exact ((ih _ (List.Perm.refl _)).cons x).trans h
  | case4 x xs y ys _ ih =>
    exact ((ih _ (List.Perm.refl _)).cons y).trans
      ((List.perm_middle (l₁ := x :: xs) (l₂ := ys) (a := y)).symm.trans h)

/-- Sorting preserves the complete list of code entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "PERM_code_sort"]
theorem codeSort_perm {α : Type} (xs : List (Nat × α)) : (codeSort xs).Perm xs := by
  fun_induction codeSort xs with
  | case1 => rfl
  | case2 => rfl
  | case3 x y rest left right =>
    apply codeMerge_imp_perm
    refine (left.append right).trans ?_
    have split := codeSplit_imp_perm rest [x] [y] (codeSplit rest [x] [y]).1
      (codeSplit rest [x] [y]).2 (Prod.eta _).symm
    simpa using split

/-- Sorting code preserves the set of mapped entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "set_MAP_code_sort"]
theorem set_map_codeSort {α β : Type} (f : Nat × α → β) (xs : List (Nat × α)) :
    {x | x ∈ (codeSort xs).map f} = {x | x ∈ xs.map f} := by
  exact Set.ext fun _ => ((codeSort_perm xs).map f).mem_iff

/-- Sorting preserves distinctness of code labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ALL_DISTINCT_code_sort"]
theorem codeSort_allDistinct {α : Type} (xs : List (Nat × α)) :
    ((codeSort xs).map Prod.fst).Nodup ↔ (xs.map Prod.fst).Nodup := by
  exact ((codeSort_perm xs).map Prod.fst).nodup_iff


/-- A permutation with distinct keys builds the same sparse code tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "PERM_IMP_fromAList_EQ_fromAList"]
theorem perm_fromAList {α : Type} (xs ys : List (Nat × α))
    (perm : xs.Perm ys) (distinct : (xs.map Prod.fst).Nodup) :
    sptFromAList xs = sptFromAList ys := by
  have distinctY : (ys.map Prod.fst).Nodup := ((perm.map Prod.fst).nodup_iff).mp distinct
  apply (sptEqThm _ _ ⟨sptWfFromAList xs, sptWfFromAList ys⟩).2
  intro k
  rw [sptLookup_sptFromAList, sptLookup_sptFromAList]
  cases hx : sptAListLookup k xs with
  | none =>
    cases hy : sptAListLookup k ys with
    | none => rfl
    | some v =>
      have memY := sptAListLookup_mem k ys v hy
      have memX : (k, v) ∈ xs := perm.mem_iff.mpr memY
      have eq := sptAListLookup_eq_of_mem_unique k v xs memX
        (fun _ hm => congrArg Prod.snd (List.inj_on_of_nodup_map distinct hm memX rfl))
      simp [hx] at eq
  | some v =>
    have memX := sptAListLookup_mem k xs v hx
    have memY : (k, v) ∈ ys := perm.mem_iff.mp memX
    exact (sptAListLookup_eq_of_mem_unique k v ys memY
      (fun _ hm => congrArg Prod.snd (List.inj_on_of_nodup_map distinctY hm memY rfl))).symm

/-- Sorting distinct-key code leaves the resulting sparse tree unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "fromAList_code_sort"]
theorem sort_fromAList {α : Type} (xs : List (Nat × α))
    (distinct : (xs.map Prod.fst).Nodup) :
    sptFromAList (codeSort xs) = sptFromAList xs := by
  apply perm_fromAList (codeSort xs) xs (codeSort_perm xs)
  exact (codeSort_allDistinct xs).mpr distinct


end Flapjack.Compiler.Backend.ClosToBvl
