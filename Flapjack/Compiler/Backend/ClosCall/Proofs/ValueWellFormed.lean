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

/-- Canonical finite-map codec for the source code map in the extension theorem. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_subg_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code code key

/-- Canonical finite-map codec for the extended code map. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_subg_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code codeNext key

/-- Extending compiler state, allowed locations, and installed code preserves
value well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_subg"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem valueWellFormed_subg (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (v : Value)
    (gNext : State) (allowedNext : Nat → Prop) (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : valueWellFormed g allowed code v ∧ code.submap codeNext ∧
      stateExtends g gNext ∧ (∀ x, allowed x → allowedNext x)) :
    valueWellFormed gNext allowedNext codeNext v := by
  cases v with
  | number n => simp [valueWellFormed]
  | word64 w => simp [valueWellFormed]
  | byteVector bytes => simp [valueWellFormed]
  | refPtr b n => simp [valueWellFormed]
  | block tag values =>
      simp only [valueWellFormed] at h ⊢
      intro value member
      exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
        ⟨h.1 value member, h.2⟩
  | closure loc values env arity body =>
      cases loc with
      | none => simp [valueWellFormed] at h
      | some loc =>
          simp only [valueWellFormed] at h ⊢
          obtain ⟨valuesSafe, envSafe, fns, related⟩ := h.1
          refine ⟨?_, ?_, fns, recClosureRel_mono g gNext allowed allowedNext code codeNext
            loc [(arity, body)] fns related h.2.1 h.2.2.1 h.2.2.2⟩
          · intro value member
            exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
              ⟨valuesSafe value member, h.2⟩
          · intro value member
            exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
              ⟨envSafe value member, h.2⟩
  | recclosure loc values env fns index =>
      cases loc with
      | none => simp [valueWellFormed] at h
      | some loc =>
          simp only [valueWellFormed] at h ⊢
          obtain ⟨valuesSafe, envSafe, fnsNext, related⟩ := h.1
          refine ⟨?_, ?_, fnsNext, recClosureRel_mono g gNext allowed allowedNext code codeNext
            loc fns fnsNext related h.2.1 h.2.2.1 h.2.2.2⟩
          · intro value member
            exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
              ⟨valuesSafe value member, h.2⟩
          · intro value member
            exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
              ⟨envSafe value member, h.2⟩
termination_by sizeOf v
decreasing_by
  all_goals subst_vars
  all_goals have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals simp_wf
  all_goals omega

/-- Canonical codec for the original code map in code-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_submap_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code code key

/-- Canonical codec for the extended code map in code-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_submap_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code codeNext key

/-- Adding code bindings preserves direct-call value well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_SUBMAP"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem valueWellFormed_submap (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (v : Value)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : valueWellFormed g allowed code v ∧ code.submap codeNext) :
    valueWellFormed g allowed codeNext v := by
  cases v with
  | number n => simp [valueWellFormed]
  | word64 w => simp [valueWellFormed]
  | byteVector bytes => simp [valueWellFormed]
  | refPtr b n => simp [valueWellFormed]
  | block tag values =>
      simp only [valueWellFormed] at h ⊢
      intro value member
      exact valueWellFormed_submap g allowed code value codeNext ⟨h.1 value member, h.2⟩
  | closure loc values env arity body =>
      cases loc with
      | none => simp [valueWellFormed] at h
      | some loc =>
          have parts := h.1
          simp only [valueWellFormed] at parts
          obtain ⟨_, _, fns, related⟩ := parts
          exact valueWellFormed_subg g allowed code _ g allowed codeNext
            ⟨h.1, h.2, recClosureRel_stateExtendsSelf g allowed code loc [(arity, body)] fns related,
              fun _ member => member⟩
  | recclosure loc values env fns index =>
      cases loc with
      | none => simp [valueWellFormed] at h
      | some loc =>
          have parts := h.1
          simp only [valueWellFormed] at parts
          obtain ⟨_, _, fnsNext, related⟩ := parts
          exact valueWellFormed_subg g allowed code _ g allowed codeNext
            ⟨h.1, h.2, recClosureRel_stateExtendsSelf g allowed code loc fns fnsNext related,
              fun _ member => member⟩
termination_by sizeOf v
decreasing_by
  all_goals subst_vars
  all_goals have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals simp_wf
  all_goals omega

/-- Canonical codec for the source map in list code-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_everyValueWellFormed_submap_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code code key

/-- Canonical codec for the extended map in list code-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_everyValueWellFormed_submap_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code codeNext key

/-- Code extension preserves well-formedness of every value in a list. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "EVERY_wfv_SUBMAP"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem everyValueWellFormed_submap (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List Value)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : (∀ v ∈ env, valueWellFormed g allowed code v) ∧ code.submap codeNext) :
    ∀ v ∈ env, valueWellFormed g allowed codeNext v := by
  intro v member
  exact valueWellFormed_submap g allowed code v codeNext ⟨h.1 v member, h.2⟩

/-- Canonical codec for the source map in list state-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_everyValueWellFormed_subg_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code code key

/-- Canonical codec for the extended map in list state-extension preservation. -/
theorem holFmapAsFiniteSupportParamWitness_everyValueWellFormed_subg_codeNext
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).lookup key = codeNext.lookup key ∧
    (ofBroad (toBroad codeNext) codeNext.finiteSupport).finiteSupport = codeNext.finiteSupport ∧
    ofBroad (toBroad codeNext) codeNext.finiteSupport = codeNext :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code codeNext key

/-- Extending the compiler state, code and allowed locations preserves
well-formedness of every value in a list. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "EVERY_wfv_subg"
  (fmap_as_finite_support_parameters := [code, codeNext])]
theorem everyValueWellFormed_subg (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List Value)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (gNext : State) (allowedNext : Nat → Prop)
    (h : (∀ v ∈ env, valueWellFormed g allowed code v) ∧ code.submap codeNext ∧
      stateExtends g gNext ∧ (∀ x, allowed x → allowedNext x)) :
    ∀ v ∈ env, valueWellFormed gNext allowedNext codeNext v := by
  intro v member
  exact valueWellFormed_subg g allowed code v gNext allowedNext codeNext ⟨h.1 v member, h.2⟩

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

/-- Extending the compiler state, allowed locations, and installed code
preserves the well-formedness of every value in a closure state. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_state_subg"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, code, codeNext])]
theorem stateValuesWellFormed_subg {C F : Type} (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (s : ClosSem.State C F)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (gNext : State) (allowedNext : Nat → Prop)
    (h : stateValuesWellFormed g allowed code s ∧ code.submap codeNext ∧
      stateExtends g gNext ∧ (∀ x, allowed x → allowedNext x)) :
    stateValuesWellFormed gNext allowedNext codeNext s := by
  obtain ⟨⟨globals, refs, empty⟩, codeSub, stateSub, allowedSub⟩ := h
  refine ⟨?_, ?_, empty⟩
  · intro entry member value found
    exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
      ⟨globals entry member value found, codeSub, stateSub, allowedSub⟩
  · intro key cell found
    apply everyRefValue_mono _ _ cell ?_ (refs key cell found)
    intro value safe
    exact valueWellFormed_subg g allowed code value gNext allowedNext codeNext
      ⟨safe, codeSub, stateSub, allowedSub⟩

/-- Adding code bindings preserves the value invariant of a closure state. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_state_SUBMAP"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, code, codeNext])]
theorem stateValuesWellFormed_submap {C F : Type} (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (s : ClosSem.State C F)
    (codeNext : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : stateValuesWellFormed g allowed code s ∧ code.submap codeNext) :
    stateValuesWellFormed g allowed codeNext s := by
  obtain ⟨⟨globals, refs, empty⟩, codeSub⟩ := h
  refine ⟨?_, ?_, empty⟩
  · intro entry member value found
    exact valueWellFormed_submap g allowed code value codeNext ⟨globals entry member value found, codeSub⟩
  · intro key cell found
    apply everyRefValue_mono _ _ cell ?_ (refs key cell found)
    intro value safe
    exact valueWellFormed_submap g allowed code value codeNext ⟨safe, codeSub⟩

/-- Canonical code-map codec for decoded-list well-formedness. -/
theorem holFmapAsFiniteSupportParamWitness_valueToList_wellFormed_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code code key

/-- Decoding a well-formed value as a list yields well-formed elements. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_to_list_wfv"
  (fmap_as_finite_support_parameters := [code])]
theorem valueToList_wellFormed (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (h : Value) (x : List Value)
    (assumptions : valueToList h = some x ∧ valueWellFormed g allowed code h) :
    ∀ v ∈ x, valueWellFormed g allowed code v := by
  cases h with
  | block tag values =>
    cases values with
    | nil =>
      simp only [valueToList] at assumptions
      split at assumptions <;> simp_all
    | cons first tail =>
      cases tail with
      | nil => simp [valueToList] at assumptions
      | cons last tail =>
        cases tail with
        | cons extra rest => simp [valueToList] at assumptions
        | nil =>
          simp only [valueToList] at assumptions
          split at assumptions <;> simp_all
          cases decoded : valueToList last with
          | none => simp [decoded] at assumptions
          | some xs =>
            simp only [decoded, Option.some.injEq] at assumptions
            obtain ⟨⟨_, rfl, rfl⟩, safe⟩ := assumptions
            simp only [valueWellFormed, List.mem_cons, forall_eq_or_imp] at safe
            have tailSafe := valueToList_wellFormed g allowed code last xs ⟨decoded, safe.2.1⟩
            simp only [List.mem_cons, forall_eq_or_imp]
            exact ⟨safe.1, tailSafe⟩
  | number n => simp [valueToList] at assumptions
  | word64 w => simp [valueToList] at assumptions
  | byteVector bytes => simp [valueToList] at assumptions
  | refPtr b n => simp [valueToList] at assumptions
  | closure loco values env arity body => simp [valueToList] at assumptions
  | recclosure loco values env fns index => simp [valueToList] at assumptions
termination_by sizeOf h
decreasing_by
  subst_vars
  simp_wf
  omega

/-- Canonical code-map codec for Boolean and unit well-formedness. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_boolUnit_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_valueWellFormed_code code key

/-- Boolean values and unit are well formed. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_Boolv"
  (fmap_as_finite_support_parameters := [code])]
theorem valueWellFormed_boolUnit (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (b : Bool) :
    valueWellFormed g allowed code (boolValue b) ∧ valueWellFormed g allowed code unitValue := by
  simp [boolValue, unitValue, valueWellFormed]

end Flapjack.Compiler.Backend.ClosCall
