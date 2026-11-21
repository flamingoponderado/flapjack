module

public import Flapjack.Compiler.Backend.DataToWord.Variables
public import Flapjack.Misc.Sptree.ToAList
public import Flapjack.Misc.Sptree.Wf
public import Mathlib.Tactic

@[expose] public section

/-! Lookup properties of the data-to-word live-set translation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack
open Classical

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

/-- Adjusted keys are even; this factors the three HOL reserved-key proofs. -/
private theorem oddNotAdjusted {α : Type} (names : Spt α) (k : Nat) (odd : k % 2 = 1) :
    ¬ sptDomain (adjustSet names) k := by
  intro member
  obtain ⟨n, eq, _⟩ := (adjustSet_domain names k).mp member
  simp only [adjustVar] at eq
  omega

/-- One is absent from every adjusted domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "NOT_1_domain"]
theorem not_one_adjustSet {α : Type} (names : Spt α) : ¬ sptDomain (adjustSet names) 1 :=
  oddNotAdjusted names 1 rfl

/-- Three is absent from every adjusted domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "NOT_3_domain"]
theorem not_three_adjustSet {α : Type} (names : Spt α) : ¬ sptDomain (adjustSet names) 3 :=
  oddNotAdjusted names 3 rfl

/-- Five is absent from every adjusted domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "NOT_5_domain"]
theorem not_five_adjustSet {α : Type} (names : Spt α) : ¬ sptDomain (adjustSet names) 5 :=
  oddNotAdjusted names 5 rfl


@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_0_adjust_set"]
theorem lookup_zero_adjustSet {α : Type} (names : Spt α) :
    sptLookup 0 (adjustSet names) = none := by
  have absent : ¬ sptDomain (adjustSet names) 0 := by
    intro member
    obtain ⟨n, eq, _⟩ := (adjustSet_domain names 0).mp member
    simp only [adjustVar] at eq
    omega
  cases h : sptLookup 0 (adjustSet names) <;> simp_all [sptDomain]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_1_adjust_set"]
theorem lookup_one_adjustSet {α : Type} (names : Spt α) :
    sptLookup 1 (adjustSet names) = none := by
  have absent := not_one_adjustSet names
  cases h : sptLookup 1 (adjustSet names) <;> simp_all [sptDomain]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_3_adjust_set"]
theorem lookup_three_adjustSet {α : Type} (names : Spt α) :
    sptLookup 3 (adjustSet names) = none := by
  have absent := not_three_adjustSet names
  cases h : sptLookup 3 (adjustSet names) <;> simp_all [sptDomain]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_5_adjust_set"]
theorem lookup_five_adjustSet {α : Type} (names : Spt α) :
    sptLookup 5 (adjustSet names) = none := by
  have absent := not_five_adjustSet names
  cases h : sptLookup 5 (adjustSet names) <;> simp_all [sptDomain]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_ODD_adjust_set"]
theorem lookup_odd_adjustSet {α : Type} (n : Nat) (names : Spt α)
    (odd : n % 2 = 1) : sptLookup n (adjustSet names) = none := by
  have absent := oddNotAdjusted names n odd
  cases h : sptLookup n (adjustSet names) <;> simp_all [sptDomain]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "wf_adjust_set"]
theorem wf_adjustSet {α : Type} (names : Spt α) : sptWf (adjustSet names) = true := by
  exact sptWfFromAList _

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_adjust_set"]
theorem lookup_adjustSet {α : Type} (n : Nat) (names : Spt α) :
    sptLookup n (adjustSet names) =
      if n % 2 = 1 ∨ n = 0 then none else
      if sptDomain names ((n - 2) / 2) then some () else none := by
  have domain : sptDomain (adjustSet names) n ↔
      n % 2 = 0 ∧ n ≠ 0 ∧ sptDomain names ((n - 2) / 2) := by
    rw [adjustSet_domain]
    constructor
    · rintro ⟨k, hk, hmem⟩
      simp only [adjustVar] at hk
      have hd : (n - 2) / 2 = k := by omega
      refine ⟨by omega, by omega, ?_⟩
      simpa [hd] using hmem
    · rintro ⟨heven, hnonzero, hmem⟩
      refine ⟨(n - 2) / 2, ?_, hmem⟩
      simp only [adjustVar]
      omega
  cases h : sptLookup n (adjustSet names) with
  | none =>
    have absent : ¬ sptDomain (adjustSet names) n := by simp [sptDomain, h]
    have absent2 := mt domain.mpr absent
    split <;> simp_all
  | some value =>
    have present : sptDomain (adjustSet names) n := by simp [sptDomain, h]
    have ⟨heven, hn, hm⟩ := domain.mp present
    have notodd : ¬ (n % 2 = 1 ∨ n = 0) := by omega
    cases value
    simp [notodd, hm]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_set_inter"]
theorem adjustSet_inter {α β : Type} (t1 : Spt α) (t2 : Spt β) :
    adjustSet (sptInter t1 t2) = sptInter (adjustSet t1) (adjustSet t2) := by
  apply (sptEqThm _ _ ⟨wf_adjustSet _, sptWfInter _ _⟩).2
  intro n
  rw [lookup_adjustSet, sptLookup_sptInterCases, lookup_adjustSet, lookup_adjustSet]
  by_cases h : n % 2 = 1 ∨ n = 0
  · simp [h]
  · simp only [h, if_false, sptDomain_sptInter]
    by_cases h1 : sptDomain t1 ((n - 2) / 2) <;>
      by_cases h2 : sptDomain t2 ((n - 2) / 2) <;> simp [h1, h2]

/-- Exact HOL `lookup_adjust_var_adjust_set_NONE`
(`data_to_word_gcProofScript.sml:400-407`); the typed capture shows an
arbitrary source payload type. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml"
  "lookup_adjust_var_adjust_set_NONE"]
theorem lookup_adjust_var_adjust_set_NONE {α : Type} {n : Nat} {s : Spt α} :
    sptLookup (adjustVar n) (adjustSet s) = none ↔ sptLookup n s = none := by
  rw [lookup_adjustSet_map]
  cases sptLookup n s <;> simp

/-- Exact HOL `lookup_adjust_var_adjust_set_SOME_UNIT`
(`data_to_word_gcProofScript.sml:409-417`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml"
  "lookup_adjust_var_adjust_set_SOME_UNIT"]
theorem lookup_adjust_var_adjust_set_SOME_UNIT {α : Type} {n : Nat} {s : Spt α} :
    sptLookup (adjustVar n) (adjustSet s) = some () ↔ (sptLookup n s).isSome = true := by
  rw [lookup_adjustSet_map]
  cases sptLookup n s <;> simp

/-- Exact HOL `IS_SOME_lookup_domain` (`data_to_word_gcProofScript.sml:518-522`);
HOL `k ∈ domain m` is `sptDomain m k`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "IS_SOME_lookup_domain"]
theorem IS_SOME_lookup_domain {α : Type} {k : Nat} {m : Spt α} :
    (sptLookup k m).isSome = true ↔ sptDomain m k :=
  Iff.rfl

/-- Exact HOL `is_some_lookup_union` (`data_to_word_gcProofScript.sml:4880-4886`,
a `[local]` theorem); `union` is the reviewed `sptUnion`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_some_lookup_union"]
theorem is_some_lookup_union {α : Type} {n : Nat} {t1 t2 : Spt α} :
    (sptLookup n (sptUnion t1 t2)).isSome = true ↔
      (sptLookup n t1).isSome = true ∨ (sptLookup n t2).isSome = true := by
  rw [sptLookup_sptUnion]
  cases sptLookup n t1 <;> simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
