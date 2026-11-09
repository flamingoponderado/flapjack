import Flapjack.Compiler.Backend.DataToWord.Variables
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Tactic

/-! Lookup properties of the data-to-word live-set translation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The adjusted live-set lookup records whether the source name exists,
independently of the source map's payload type. This helper generalizes the
source's unit-valued live-set theorem. -/
theorem lookup_adjustSet_map {α : Type} (n : Nat) (names : Spt α) :
    sptLookup (adjustVar n) (adjustSet names) = (sptLookup n names).map (fun _ => ()) := by
  rw [adjustSet, sptLookup_sptFromAList]
  cases found : sptLookup n names with
  | none =>
    simp only [Option.map_none]
    cases h : sptAListLookup (adjustVar n) ((sptToAList names).map fun (key, _) => (adjustVar key, ())) with
    | none => rfl
    | some value =>
      have member := sptAListLookup_mem _ _ _ h
      obtain ⟨⟨key, sourceValue⟩, entry, equal⟩ := List.mem_map.mp member
      have same : key = n := by
        have keyEq : adjustVar key = adjustVar n := by simpa using congrArg Prod.fst equal
        simp only [adjustVar] at keyEq
        omega
      subst key
      have present := (sptMemToAList names n sourceValue).mp entry
      rw [found] at present
      contradiction
  | some value =>
    simp only [Option.map_some]
    apply sptAListLookup_eq_of_mem_unique
    · apply List.mem_map.mpr
      exact ⟨(n, value), (sptMemToAList names n value).mpr found, rfl⟩
    · intro other _
      cases other
      rfl

/-- Every adjusted live name comes from exactly a translated source name.
This generalized domain characterization is Flapjack proof infrastructure. -/
theorem adjustSet_domain {α : Type} (names : Spt α) (key : Nat) :
    sptDomain (adjustSet names) key ↔ ∃ n, key = adjustVar n ∧ sptDomain names n := by
  rw [adjustSet, sptDomainFromAList]
  simp only [List.map_map, Function.comp_apply, List.mem_map]
  constructor
  · rintro ⟨⟨n, value⟩, member, equal⟩
    exact ⟨n, equal.symm, (sptMem_iff_lookup n names).mpr
      ⟨value, (sptMemToAList names n value).mp member⟩⟩
  · rintro ⟨n, equal, present⟩
    obtain ⟨value, lookup⟩ := (sptMem_iff_lookup n names).mp present
    exact ⟨(n, value), (sptMemToAList names n value).mpr lookup, equal.symm⟩

/-- Adjusting a unit-valued live set preserves lookup at translated names.
The typed HOL capture confirms the source set is unit-valued. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_adjust_var_adjust_set"]
theorem lookup_adjustVar_adjustSet (n : Nat) (names : NumSet) :
    sptLookup (adjustVar n) (adjustSet names) = sptLookup n names := by
  rw [lookup_adjustSet_map]
  cases sptLookup n names <;> simp

/-- A source name belongs to the live set exactly when its translated name
belongs to the adjusted set. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_IN_adjust_set"]
theorem adjustVar_mem_adjustSet (n : Nat) (names : NumSet) :
    sptDomain (adjustSet names) (adjustVar n) ↔ sptDomain names n := by
  simp [sptDomain, lookup_adjustVar_adjustSet]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
