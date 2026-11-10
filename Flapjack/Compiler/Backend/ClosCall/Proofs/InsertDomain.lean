module

public import Flapjack.Compiler.Backend.ClosCall.InsertEach
public import Mathlib.Data.Set.Defs

@[expose] public section

/-! Direct-call location insertion and its sparse-tree domain. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- Inserting known locations leaves the state payload unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "SND_insert_each"]
theorem insertEach_snd {A : Type} (loc count : Nat) (state : NumSet × A) :
    (insertEachSource loc count state).2 = state.2 := by
  induction count generalizing loc state with
  | zero => rfl
  | succ count ih =>
    cases state with
    | mk known payload =>
      exact ih (loc + 2) (sptInsert loc () known, payload)

/-- The location component does not depend on either state payload. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "FST_insert_each_same"]
theorem insertEach_fst_same {A B : Type} (loc count : Nat) (g0 : NumSet × A) (g1 : NumSet × B)
    (same : g0.1 = g1.1) : (insertEachSource loc count g0).1 = (insertEachSource loc count g1).1 := by
  induction count generalizing loc g0 g1 with
  | zero => exact same
  | succ count ih =>
    cases g0 with
    | mk known payload =>
      cases g1 with
      | mk known' payload' =>
        simp only at same
        subst known'
        exact ih (loc + 2) (sptInsert loc () known, payload) (sptInsert loc () known, payload') rfl

/-- Inserting locations uses only the first component of the input pair. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "insert_each_pair_arg"]
theorem insertEach_pair_arg {A B : Type} (loc count : Nat) (known : NumSet) (payload : A) (other : B) :
    insertEachSource loc count (known, payload) =
      ((insertEachSource loc count (known, other)).1, payload) := by
  apply Prod.ext
  · exact insertEach_fst_same loc count _ _ rfl
  · exact insertEach_snd loc count _

/-- Inserting the successive locations adds exactly their generated set to
the known-location domain. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "domain_FST_insert_each"]
theorem domain_insertEach {A : Type} (p n : Nat) (g : NumSet × A) :
    sptDomain (insertEachSource p n g).1 =
      {x | x ∈ (List.range n).map (fun i => 2 * i + p)} ∪ sptDomain g.1 := by
  induction n generalizing p g with
  | zero =>
    funext x
    apply propext
    change sptDomain g.1 x ↔ (x ∈ ([] : List Nat) ∨ sptDomain g.1 x)
    simp
  | succ n ih =>
    cases g with
    | mk known payload =>
      simp only [insertEachSource, ih]
      funext x
      apply propext
      simp only [List.mem_map, List.mem_range]
      change (∃ i, i < n ∧ 2 * i + (p + 2) = x) ∨ sptMem x (sptInsert p () known) ↔
        (∃ i, i < n + 1 ∧ 2 * i + p = x) ∨ sptMem x known
      rw [sptMem_sptInsert]
      constructor
      · rintro (⟨i, hi, eq⟩ | eq | old)
        · left; refine ⟨i + 1, by omega, ?_⟩; omega
        · left; refine ⟨0, by omega, ?_⟩; omega
        · exact Or.inr old
      · rintro (⟨i, hi, eq⟩ | old)
        · by_cases zero : i = 0
          · exact Or.inr (Or.inl (by omega))
          · left; refine ⟨i - 1, by omega, ?_⟩; omega
        · exact Or.inr (Or.inr old)

/-- Inserting locations preserves the existing sparse set. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "insert_each_subspt"]
theorem insertEach_subspt {A : Type} (p n : Nat) (g : NumSet × A) :
    sptSubspt g.1 (insertEachSource p n g).1 := by
  intro key old
  have new : sptMem key (insertEachSource p n g).1 := by
    change sptDomain (insertEachSource p n g).1 key
    rw [domain_insertEach]
    exact Or.inr old
  refine ⟨new, ?_⟩
  obtain ⟨v, hv⟩ := (sptMem_iff_lookup key g.1).1 old
  obtain ⟨w, hw⟩ := (sptMem_iff_lookup key (insertEachSource p n g).1).1 new
  cases v
  cases w
  rw [hv, hw]

end Flapjack.Compiler.Backend.ClosCall
