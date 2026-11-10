module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call well-formedness for closure values. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Apply a value predicate to each value contained in a reference cell. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "every_refv_def"]
def everyRefValue {α : Type} (P : α → Prop) : ClosSem.Ref α → Prop
  | .valueArray vs => ∀ v ∈ vs, P v
  | .thunk _ v => P v
  | .byteArray _ => True

/-- Reference-cell predicates are monotone in their value predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "every_refv_mono"]
theorem everyRefValue_mono {α : Type} (P P' : α → Prop) (v : ClosSem.Ref α)
    (h : ∀ x, P x → P' x) (safe : everyRefValue P v) : everyRefValue P' v := by
  cases v with
  | valueArray values => exact fun x member => h x (safe x member)
  | thunk mode value => exact h value safe
  | byteArray bytes => trivial

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the value well-formedness code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Direct-call well-formedness requires located closures, recursively
well-formed captured values, and a corresponding transformed function group. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_def"
  (fmap_as_finite_support_parameters := [code])]
def valueWellFormed (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Value → Prop
  | .closure none _ _ _ _ | .recclosure none _ _ _ _ => False
  | .closure (some loc) vs env n body =>
      (∀ v ∈ vs, valueWellFormed g allowed code v) ∧
      (∀ v ∈ env, valueWellFormed g allowed code v) ∧
      ∃ fns2, recClosureRel g allowed code loc [(n, body)] fns2
  | .recclosure (some loc) vs env fns _ =>
      (∀ v ∈ vs, valueWellFormed g allowed code v) ∧
      (∀ v ∈ env, valueWellFormed g allowed code v) ∧
      ∃ fns2, recClosureRel g allowed code loc fns fns2
  | .block _ vs => ∀ v ∈ vs, valueWellFormed g allowed code v
  | _ => True
termination_by value => sizeOf value
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals simp_wf
  all_goals omega

/-- Closure-state finite maps roundtrip through their lookup/support view. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Well-formed source states have well-formed globals and stored values,
and contain no installed code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_state_def"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, code])]
def stateValuesWellFormed {C F : Type} (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (s : ClosSem.State C F) : Prop :=
  (∀ entry ∈ s.globals, ∀ value, entry = some value → valueWellFormed g allowed code value) ∧
  (∀ key cell, s.refs.lookup key = some cell → everyRefValue (valueWellFormed g allowed code) cell) ∧
  s.code = HolFiniteMapExact.empty

end Flapjack.Compiler.Backend.ClosCall
