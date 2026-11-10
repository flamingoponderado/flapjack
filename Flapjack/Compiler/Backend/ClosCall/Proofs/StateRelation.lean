module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations
public import Flapjack.Misc.Option.Rel

@[expose] public section

/-! Direct-call simulation relation between closure states. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- Closure-state finite maps roundtrip through their lookup/support view. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Source and target states agree on observations and contain related
globals and reference cells; the source code map is empty. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
def stateRel {C F : Type} (g : State) (allowed : Nat → Prop)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) : Prop :=
  source.ffi = target.ffi ∧ source.clock = target.clock ∧ source.maxApp = target.maxApp ∧
  List.Forall₂ (optionRel (valueRel g allowed target.code)) source.globals target.globals ∧
  (∀ key, optionRel (ClosProps.refRel (valueRel g allowed target.code))
    (source.refs.lookup key) (target.refs.lookup key)) ∧
  source.code = HolFiniteMapExact.empty

/-- Related states have the same maximum application arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_rel_max_app"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem stateRel_maxApp {C F : Type} (g : State) (allowed : Nat → Prop)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (h : stateRel g allowed source target) : source.maxApp = target.maxApp := h.2.2.1

/-- Related states have the same clock. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_rel_clock"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem stateRel_clock {C F : Type} (g : State) (allowed : Nat → Prop)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (h : stateRel g allowed source target) : source.clock = target.clock := h.2.1

/-- Setting both clocks to the same value preserves the relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem stateRel_withClock {C F : Type} (g : State) (allowed : Nat → Prop)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (clock : Nat) (h : stateRel g allowed source target) :
    stateRel g allowed { source with clock := clock } { target with clock := clock } := by
  exact ⟨h.1, rfl, h.2.2⟩

/-- A source reference in related states has a related target reference. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_rel_flookup_refs"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem stateRel_lookupRefs {C F : Type} (g : State) (allowed : Nat → Prop)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (key : Nat) (value : ClosSem.Ref ClosSem.Value)
    (h : stateRel g allowed source target ∧ source.refs.lookup key = some value) :
    ∃ value', target.refs.lookup key = some value' ∧
      ClosProps.refRel (valueRel g allowed target.code) value value' := by
  have rel := h.1.2.2.2.2.1 key
  rw [h.2] at rel
  cases found : target.refs.lookup key with
  | none => simp [optionRel, found] at rel
  | some value' => exact ⟨value', rfl, by simpa [optionRel, found] using rel⟩

end Flapjack.Compiler.Backend.ClosCall
