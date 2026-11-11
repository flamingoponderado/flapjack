module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.MakeState
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.Misc.ShiftSeq
public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call compiler oracle invariant. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- Oracle monotonicity over a union is equivalent to monotonicity over each part. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "oracle_monotonic_init_UNION"]
theorem oracleMonotonic_initUnion {A B : Type} (f : A → Set B) (R : B → B → Prop)
    (initial1 initial2 : Set B) (co : Nat → A) :
    BackendProps.oracleMonotonic f R (initial1 ∪ initial2) co ↔
      BackendProps.oracleMonotonic f R initial1 co ∧ BackendProps.oracleMonotonic f R initial2 co := by
  simp only [BackendProps.oracleMonotonic, Set.mem_union, or_imp, forall_and]
  tauto

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The oracle invariant's code map uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_oracleOk_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- The first k oracle entries can be compiled with consistent state and code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "co_ok_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def oracleOk {A B : Type} (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) (fullGs : Nat → State) (k : Nat) : Prop :=
  if k = 0 then True else
    let g := (co 0).1.1
    let program := co 0
    let compiled := compileInc g (program.2.1, program.2.2)
    (co 1).1.1 = compiled.1 ∧
    makeState g code = some (fullGs 0) ∧
    (∀ i, stateExtends (fullGs 0) (fullGs i)) ∧
    (∀ x i, x ∈ codeLocations program.2.1 ∧ ¬ sptDomain compiled.1 x →
      ¬ sptDomain (co i).1.1 x) ∧
    (∀ x, ¬ (x ∈ codeLocations program.2.1 ∧ sptDomain g x)) ∧
    (∀ x, ¬ (x ∈ code.domain ∧ x ∈ compiled.2.2.map Prod.fst)) ∧
    (compiled.2.2.map Prod.fst).Nodup ∧
    oracleOk (code.updateListEq compiled.2.2) (holShiftSeq 1 co) (holShiftSeq 1 fullGs) (k - 1)
termination_by k
decreasing_by omega

/-- Canonical finite-map codec for the oracle state-alignment theorem. -/
theorem holFmapAsFiniteSupportParamWitness_oracleOk_fullState_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_oracleOk_code code key

/-- The oracle's compiler state agrees with the corresponding full state. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "co_ok_IMP_full_gs_eq_shift_seq"
  (fmap_as_finite_support_parameters := [code])]
theorem oracleOk_fullState {A B G : Type} (k : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) (_g : G) (fullGs : Nat → State)
    (h : oracleOk code co fullGs (k + 1)) :
    (holShiftSeq k co 0).1.1 = (fullGs k).1 := by
  induction k generalizing code co fullGs with
  | zero =>
    rw [oracleOk] at h
    simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self] at h
    obtain ⟨_, made, _⟩ := h
    unfold makeState at made
    split at made
    · simp only [Option.some.injEq] at made
      simpa [holShiftSeq] using congrArg Prod.fst made
    · simp at made
  | succ k ih =>
    rw [oracleOk] at h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h
    obtain ⟨_, _, _, _, _, _, _, rest⟩ := h
    have result := ih _ _ _ rest
    simpa [holShiftSeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- Canonical finite-map codec for the oracle well-formedness theorem. -/
theorem holFmapAsFiniteSupportParamWitness_oracleOk_wellFormed_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_oracleOk_code code key

/-- Every full state covered by the oracle invariant is well formed. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "co_ok_IMP_wfg_full_gs"
  (fmap_as_finite_support_parameters := [code])]
theorem oracleOk_wellFormed {A B G : Type} (k : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) (_g : G) (fullGs : Nat → State)
    (h : oracleOk code co fullGs (k + 1)) : wellFormed (fullGs k) := by
  induction k generalizing code co fullGs with
  | zero =>
    rw [oracleOk] at h
    simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self] at h
    exact makeState_wellFormed _ _ _ h.2.1
  | succ k ih =>
    rw [oracleOk] at h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h
    obtain ⟨_, _, _, _, _, _, _, rest⟩ := h
    have result := ih _ _ _ rest
    simpa [holShiftSeq, Nat.add_comm] using result

/-- Canonical finite-map codec for the existential construction witness. -/
theorem holFmapAsFiniteSupportExistentialWitness_oracleOk_makeState_code2
    (code2 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad code2)).lookup = code2.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad code2)).finiteSupport = code2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad code2) = code2 := by
  cases code2
  exact ⟨rfl, rfl, rfl⟩

/-- Each full state covered by the oracle invariant is constructed from code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "co_ok_IMP_make_g"
  (fmap_as_finite_support_relation := [code]) (fmap_as_finite_support_existentials := [code2])]
theorem oracleOk_makeState {A B G : Type} (k : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (co : Nat → (NumSet × A) × List ClosLang.Exp × B) (_g : G) (fullGs : Nat → State)
    (h : oracleOk code co fullGs (k + 1)) :
    ∃ d : NumSet, ∃ code2 : HolFiniteMapExact Nat (Nat × ClosLang.Exp),
      makeState d code2 = some (fullGs k) := by
  induction k generalizing code co fullGs with
  | zero =>
    rw [oracleOk] at h
    simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self] at h
    exact ⟨(co 0).1.1, code, h.2.1⟩
  | succ k ih =>
    rw [oracleOk] at h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h
    obtain ⟨_, _, _, _, _, _, _, rest⟩ := h
    have result := ih _ _ _ rest
    simpa [holShiftSeq, Nat.add_comm] using result

end Flapjack.Compiler.Backend.ClosCall
