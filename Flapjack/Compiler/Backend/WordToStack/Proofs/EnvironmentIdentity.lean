import Flapjack.Compiler.Backend.WordToStack.Proofs.KeyValueOrder
import Flapjack.Basis.Pure.MlList.SortPerm
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack

namespace Flapjack.WordToStackProofs

/-- Flapjack support for the identity oracle: actual guarded rearrangement
preserves every input list without a supplied permutation premise. -/
theorem listRearrangeIdentity {α : Type} (xs : List α) :
    wordSemListRearrange id xs = xs := by
  unfold wordSemListRearrange
  split
  · apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  · rfl

/-- Flapjack support: actual comparator sorting is strict key sorting when
the key list has no duplicates. Payload tie-breakers remain unrestricted. -/
theorem comparatorSortedStrict {width : Nat} [NeZero width]
    (xs : List (Nat × WordLocW width))
    (sorted : holSorted (fun x y => wordSemKeyValCompare x y = true) xs)
    (unique : (xs.map Prod.fst).Nodup) :
    holSorted (fun x y => x.1 > y.1) xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    cases xs with
    | nil => trivial
    | cons y ys =>
      simp only [holSorted] at sorted ⊢
      simp only [List.map_cons, List.nodup_cons] at unique
      have different : x.1 ≠ y.1 := by
        intro eq
        apply unique.1
        simp [eq]
      have order : x.1 > y.1 := by
        rcases x with ⟨a, x⟩
        rcases y with ⟨b, y⟩
        have compared := sorted.1
        simp [wordSemKeyValCompare, different] at compared
        exact compared
      exact ⟨order, ih sorted.2 (by simpa only [List.map_cons, List.nodup_cons] using unique.2)⟩

/-- Full original identity-oracle environment result: strict descending keys,
unchanged identity oracle, and complete original tree enumeration permutation.
The sole premise is the actual env_to_list output equation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "env_to_list_K_I_IMP"
  (words_as_type_indexed_bitvec)]
theorem envToListIdentityImp {width : Nat} [NeZero width]
    (env : Spt (WordLocW width)) (entries : List (Nat × WordLocW width))
    (oracle : Nat → Nat → Nat)
    (output : wordSemEnvToList env (fun _ => id) = (entries, oracle)) :
    holSorted (fun x y => x.1 > y.1) entries ∧ oracle = (fun _ => id) ∧
      holPerm (sptToAList env) entries := by
  simp only [wordSemEnvToList, listRearrangeIdentity, Prod.mk.injEq] at output
  obtain ⟨rfl, rfl⟩ := output
  have permutation := Basis.Pure.MlList.sortPerm wordSemKeyValCompare (sptToAList env)
  have unique := sptAllDistinctMapFstToAList env
  have uniqueSorted := ((holPerm_iff _ _).mp permutation).map Prod.fst
  have sorted := Basis.Pure.MlList.sortSorted wordSemKeyValCompare (sptToAList env)
    ⟨fun x y z pair => Compiler.Backend.WordToStack.transitiveKeyValCompare x y z pair.1 pair.2,
     Compiler.Backend.WordToStack.totalKeyValCompare⟩
  exact ⟨comparatorSortedStrict _ sorted (uniqueSorted.nodup_iff.mp unique), rfl, permutation⟩

end Flapjack.WordToStackProofs
