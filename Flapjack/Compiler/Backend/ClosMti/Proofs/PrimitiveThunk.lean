module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveCopy
public import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveFfi

@[expose] public section

/-! Ordinary thunk operations for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Related values and stores agree on the thunk-update validity check. -/
theorem badThunkUpdate_related {C F : Type} (source target : State C F)
    (mode : AstHOL.ThunkMode) (value nextValue : Value)
    (valueRel : ValueRel source.maxApp value nextValue) (states : StateRel source target) :
    badThunkUpdate mode value source.refs = badThunkUpdate mode nextValue target.refs := by
  have related := destThunk_related states (List.Forall₂.cons valueRel List.Forall₂.nil)
  unfold badThunkUpdate
  split
  · cases left : destThunk [value] source.refs <;> cases right : destThunk [nextValue] target.refs <;>
      simp_all <;> cases related
  · rfl

/-- Thunk allocation preserves the validity check, address and stored value. -/
theorem primitiveSimulation_thunk_alloc {C F : Type} (mode : AstHOL.ThunkMode) :
    @PrimitiveSimulation C F (.thunkOp (.allocThunk mode)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have same := badThunkUpdate_related source target mode value nextValue head states
      cases bad : badThunkUpdate mode value source.refs with
      | true => simp [doApp, ← same, bad, excRel]
      | false =>
        have addressEq := stateRel_leastUnusedRef states
        have refs := stateRel_updateRefs states (leastUnusedRef source.refs)
          (.thunk mode value) (.thunk mode nextValue) (.thunk mode value nextValue head)
        have pointerRel : ValueRel source.maxApp (.refPtr false (leastUnusedRef source.refs))
            (.refPtr false (leastUnusedRef source.refs)) := .refPtr _ _
        simp [doApp, ← same, bad, ← addressEq, pointerRel, refs]
    | cons head tail => simp [doApp, excRel]

/-- Updating an unevaluated thunk preserves related contents and rejects
invalid pointers, modes and values on both sides. -/
theorem primitiveSimulation_thunk_update {C F : Type} (mode : AstHOL.ThunkMode) :
    @PrimitiveSimulation C F (.thunkOp (.updateThunk mode)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | refPtr flag index =>
          cases flag with
          | true => simp [doApp, excRel]
          | false =>
            rename_i value nextValue
            have same := badThunkUpdate_related source target mode value nextValue second states
            cases bad : badThunkUpdate mode value source.refs with
            | true => simp [doApp, ← same, bad, excRel]
            | false =>
              have lookup := stateRel_lookupRefs states index
              cases l : source.refs.lookup index with
              | none => cases r : target.refs.lookup index <;> simp_all [optionRel, doApp, excRel]
              | some leftRef =>
                cases r : target.refs.lookup index with
                | none => simp_all [optionRel]
                | some rightRef =>
                  have refs : RefRel source.maxApp leftRef rightRef := by simpa [optionRel, l, r] using lookup
                  cases refs with
                  | byteArray bytes => simp [doApp, ← same, bad, l, r, excRel]
                  | valueArray fields nextFields rel => simp [doApp, ← same, bad, l, r, excRel]
                  | thunk previous old next rel =>
                    cases previous with
                    | evaluated => simp [doApp, ← same, bad, l, r, excRel]
                    | notEvaluated =>
                      have refs := stateRel_updateRefs states index (.thunk mode value)
                        (.thunk mode nextValue) (.thunk mode value nextValue second)
                      have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
                      simp [doApp, ← same, bad, l, r, unitRel, refs]
        | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
          simp [doApp, excRel]
      | cons head tail => simp [doApp, excRel]

namespace DoAppLemma
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end DoAppLemma

/-- Primitive application preserves related values, states, and errors. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "do_app_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem doAppLemma {C F : Type} (source target : State C F) (left right : List Value)
    (op : ClosLang.Op) (premises : StateRel source target ∧
      List.Forall₂ (ValueRel source.maxApp) left right) :
    match doApp op right target with
    | .err targetError => ∃ sourceError,
        doApp op left source = .err sourceError ∧
        excRel (ValueRel source.maxApp) sourceError targetError
    | .val (targetValue, targetFinal) => ∃ sourceValue sourceFinal,
        ValueRel source.maxApp sourceValue targetValue ∧ StateRel sourceFinal targetFinal ∧
        doApp op left source = .val (sourceValue, sourceFinal) := by
  have allOps : @PrimitiveSimulation C F op := by
    cases op with
    | install =>
      intro source target left right states values
      simp [doApp, excRel]
    | label _ =>
      intro source target left right states values
      simp [doApp, excRel]
    | ffi name => exact primitiveSimulation_ffi name
    | intOp operation => exact primitiveSimulation_int operation
    | wordOp operation => exact primitiveSimulation_word operation
    | blockOp operation => exact primitiveSimulation_block operation
    | globOp operation => exact primitiveSimulation_global operation
    | memOp operation => exact primitiveSimulation_memory operation
    | thunkOp operation =>
      cases operation with
      | forceThunk =>
        intro source target left right states values
        simp [doApp, excRel]
      | allocThunk mode => exact primitiveSimulation_thunk_alloc mode
      | updateThunk mode => exact primitiveSimulation_thunk_update mode
  exact allOps source target left right premises.1 premises.2

/-- Every ordinary operation preserves the clock-bounded simulation. -/
theorem evaluateRel_allOrdinaryWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (targetArgs sourceCode : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode targetArgs) :
    @EvaluateRelWithin C F limit sourceCode [.op trace op targetArgs] :=
  evaluateRel_ordinaryWithin limit trace op targetArgs sourceCode notInstall notForce argsIH
    (fun source target left right states values => doAppLemma source target left right op ⟨states, values⟩)

end Flapjack.Compiler.Backend.ClosMti
