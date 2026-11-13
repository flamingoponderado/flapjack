module

public import Flapjack.Compiler.Backend.Semantics.BviSem.Semantics

@[expose] public section
namespace Flapjack.Compiler.Backend.BviInline.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.SemanticPrimitivesHOL

namespace InitialStateCarrier
/-- The BVI reference state and its finite-support representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end InitialStateCarrier

/-- Non-failing semantics excludes fatal initial evaluations at every clock. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "semantics_not_Fail_cond"
  (fmap_as_finite_support := [refs])]
theorem notFailCondition {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp))
    (co : BviSem.CompileOracle C) (cc : BviSem.Compiler C) (start : Nat)
    (h : BviSem.semantics ffi code co cc start ≠ .fail) :
    ¬ ∃ j e, (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
      (BviSem.initialState ffi code co cc j : BviSem.BviState C F))).1 = .err e ∧
      e ≠ .abort .timeoutError ∧ ∀ f, e ≠ .abort (.ffiError f) := by
  intro bad
  apply h
  simp [BviSem.semantics, bad]

/-- Non-failing semantics excludes type errors in every initial evaluation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "semantics_no_type_error"
  (fmap_as_finite_support := [refs])]
theorem semanticsNoTypeError {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp))
    (co : BviSem.CompileOracle C) (cc : BviSem.Compiler C) (start : Nat)
    (h : BviSem.semantics ffi code co cc start ≠ .fail) :
    ∀ j, (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
      (BviSem.initialState ffi code co cc j : BviSem.BviState C F))).1 ≠ .err (.abort .typeError) := by
  intro j bad
  exact notFailCondition ffi code co cc start h ⟨j, .abort .typeError, bad, by simp, by simp⟩

/-- Non-failing semantics permits only timeout or FFI errors. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "semantics_error_cases"
  (fmap_as_finite_support := [refs])]
theorem errorCases {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp))
    (co : BviSem.CompileOracle C) (cc : BviSem.Compiler C) (start : Nat)
    (h : BviSem.semantics ffi code co cc start ≠ .fail) :
    ∀ (j : Nat) (e : ErrorResult BviSem.ExnOrRet) (t : BviSem.BviState C F),
      BviSem.evaluateTuple ([.call 0 (some start) [] none], [], BviSem.initialState ffi code co cc j) = (.err e,t) →
      e = .abort .timeoutError ∨ ∃ f, e = .abort (.ffiError f) := by
  intro j e t run
  by_cases timeout : e = .abort .timeoutError
  · exact Or.inl timeout
  · right
    by_contra noFfi
    apply notFailCondition ffi code co cc start h
    refine ⟨j, e, ?_, timeout, ?_⟩
    · simp [run]
    · intro f equal
      exact noFfi ⟨f, equal⟩

/-- Non-timeout initial evaluations agree on result and final FFI state. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "semantics_terminate_unique"
  (fmap_as_finite_support := [refs])]
theorem terminateUnique {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvi.Exp))
    (co : BviSem.CompileOracle C) (cc : BviSem.Compiler C) (start k1 : Nat)
    (r1 : BviSem.BviResult) (t1 : BviSem.BviState C F) (k2 : Nat)
    (r2 : BviSem.BviResult) (t2 : BviSem.BviState C F)
    (h : BviSem.evaluateTuple ([.call 0 (some start) [] none], [], BviSem.initialState ffi code co cc k1) = (r1,t1) ∧
      BviSem.evaluateTuple ([.call 0 (some start) [] none], [], BviSem.initialState ffi code co cc k2) = (r2,t2) ∧
      r1 ≠ .err (.abort .timeoutError) ∧ r2 ≠ .err (.abort .timeoutError)) :
    r1 = r2 ∧ t1.ffi = t2.ffi := by
  obtain ⟨run1, run2, ok1, ok2⟩ := h
  have first := BviProps.evaluate_addClock [.call 0 (some start) [] none] []
    (BviSem.initialState ffi code co cc k1) t1 r1 k2 run1 ok1
  have second := BviProps.evaluate_addClock [.call 0 (some start) [] none] []
    (BviSem.initialState ffi code co cc k2) t2 r2 k1 run2 ok2
  have same : { BviSem.initialState ffi code co cc k1 with clock := k1 + k2 } =
      { BviSem.initialState ffi code co cc k2 with clock := k2 + k1 } := by
    simp [BviSem.initialState, Nat.add_comm]
  change BviSem.evaluate _ _ { BviSem.initialState ffi code co cc k1 with clock := k1 + k2 } = _ at first
  change BviSem.evaluate _ _ { BviSem.initialState ffi code co cc k2 with clock := k2 + k1 } = _ at second
  rw [same, second] at first
  exact ⟨(congrArg Prod.fst first).symm, (congrArg (fun p => p.2.ffi) first).symm⟩
end Flapjack.Compiler.Backend.BviInline.Proofs
