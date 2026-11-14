module

public import Flapjack.Misc.List
public import Flapjack.Misc.Option.Rel
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyMemory
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section

/-! State relation for the closure-numbering simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Relate closure reference payloads using the numbering value relation. -/
def RefRel (maxApp : Nat) : Ref Value → Ref Value → Prop
  | .valueArray left, .valueArray right => List.Forall₂ (ValueRel maxApp) left right
  | .byteArray left, .byteArray right => left = right
  | .thunk leftMode left, .thunk rightMode right => leftMode = rightMode ∧ ValueRel maxApp left right
  | _, _ => False

/-- Pointwise option lifting states the same domain equality and related
lookup results as HOL's finite-map relation. This helper has no separate HOL
declaration. -/
theorem optionRel_lookup_iff {K A B : Type} (relation : A → B → Prop)
    (left : HolFiniteMapExact K A) (right : HolFiniteMapExact K B) :
    (∀ key, optionRel relation (left.lookup key) (right.lookup key)) ↔
      (∀ key, (∃ value, left.lookup key = some value) ↔
        ∃ value, right.lookup key = some value) ∧
      (∀ key a b, left.lookup key = some a → right.lookup key = some b → relation a b) := by
  constructor
  · intro h
    constructor
    · intro key
      specialize h key
      cases leftEq : left.lookup key <;> cases rightEq : right.lookup key <;>
        simp_all [optionRel]
    · intro key a b ha hb
      simpa [ha, hb, optionRel] using h key
  · intro ⟨domains, entries⟩ key
    have same := domains key
    cases leftEq : left.lookup key with
    | none =>
      cases rightEq : right.lookup key with
      | none => trivial
      | some b => simp [leftEq, rightEq] at same
    | some a =>
      cases rightEq : right.lookup key with
      | none => simp [leftEq, rightEq] at same
      | some b => exact entries key a b leftEq rightEq

namespace StateRelationPort
/-- The closure state retains both finite maps through the canonical view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end StateRelationPort

/-- Numbering state relation over canonical finite-support maps. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source : State (Nat × C) F) (target : State C F) : Prop :=
  source.clock = target.clock ∧ source.ffi = target.ffi ∧ target.maxApp = source.maxApp ∧
  source.compile = stateCc (ignoreTable compileInc) target.compile ∧
  target.compileOracle = stateCo (ignoreTable compileInc) source.compileOracle ∧
  (∀ key, optionRel (RefRel source.maxApp) (source.refs.lookup key) (target.refs.lookup key)) ∧
  List.Forall₂ (optionRel (ValueRel source.maxApp)) source.globals target.globals ∧
  (∀ index, (source.compileOracle index).2.2 = [] ∧
    ¬ ClosProps.containsAppSome source.maxApp (source.compileOracle index).2.1) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty

/-- Related states have equal maximum application arities. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_max_app"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_maxApp {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (related : StateRel source target) : source.maxApp = target.maxApp :=
  related.2.2.1.symm

/-- Related states have equal clocks. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_clock"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_clock {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (related : StateRel source target) : source.clock = target.clock :=
  related.1

/-- Related states have pointwise-related global stores. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_globals"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_globals {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (related : StateRel source target) :
    List.Forall₂ (optionRel (ValueRel source.maxApp)) source.globals target.globals :=
  related.2.2.2.2.2.2.1

/-- Related states have corresponding reference maps at the target bound.
The pointwise option relation is equivalent to the source finite-map
relation by `optionRel_lookup_iff`. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_refs"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_refs {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (related : StateRel source target) :
    ∀ key, optionRel (RefRel target.maxApp) (source.refs.lookup key) (target.refs.lookup key) := by
  simpa only [related.2.2.1] using related.2.2.2.2.2.1

/-- Both related states have empty code maps. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_code"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_code {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (related : StateRel source target) :
    source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty :=
  ⟨related.2.2.2.2.2.2.2.2.1, related.2.2.2.2.2.2.2.2.2⟩

/-- Updating both clocks preserves the numbering state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_withClock {C F : Type} (clock : Nat) {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  simpa [StateRel] using related.2

/-- Replacing both global stores with pointwise-related stores preserves all
    other components of the numbering state relation. -/
theorem stateRel_withGlobals {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (sourceGlobals targetGlobals : List (Option Value)) (related : StateRel source target)
    (globalsRel : List.Forall₂ (optionRel (ValueRel source.maxApp)) sourceGlobals targetGlobals) :
    StateRel { source with globals := sourceGlobals } { target with globals := targetGlobals } := by
  rcases related with ⟨clock, ffi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  exact ⟨clock, ffi, maxApp, compiler, oracle, refs, globalsRel, safe, sourceCode, targetCode⟩

/-- Writing related references at the same address preserves the reference
    store and the rest of the numbering state relation. -/
theorem stateRel_updateRefs {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (index : Nat) (left right : Ref Value) (related : StateRel source target)
    (refRel : RefRel source.maxApp left right) :
    StateRel { source with refs := source.refs.updateEq (index, left) }
      { target with refs := target.refs.updateEq (index, right) } := by
  rcases related with ⟨clock, ffi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  refine ⟨clock, ffi, maxApp, compiler, oracle, ?_, globals, safe, sourceCode, targetCode⟩
  intro key
  by_cases equal : key = index
  · simp [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, equal, optionRel, refRel]
  · simpa [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, equal] using refs key

/-- Replacing both FFI states by the same state preserves the relation. -/
theorem stateRel_withFfi {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (ffi : Flapjack.HolFfiState F) (related : StateRel source target) :
    StateRel { source with ffi := ffi } { target with ffi := ffi } := by
  rcases related with ⟨clock, oldFfi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  exact ⟨clock, rfl, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩

end Flapjack.Compiler.Backend.ClosNumber
