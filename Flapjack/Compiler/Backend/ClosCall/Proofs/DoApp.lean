module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueWellFormed
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

@[expose] public section

/-! Direct-call primitive-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesProps

private theorem doApp_error_shape {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : ClosSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult Value)
    (run : doApp op args state = .err error) :
    error = .abort .typeError ∨ ∃ event, error = .abort (.ffiError event) := by
  cases op <;> simp only [doApp] at run
  all_goals repeat' first | split at run | simp_all
  right
  exact ⟨_, run.symm⟩

namespace DoAppPort

/-- Closure-state finite maps roundtrip through their lookup/support view. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end DoAppPort

/-- Primitive operations preserve well-formedness and simulate direct-call conversion. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "do_app_thm"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem doApp_correct {C F : Type} (op : ClosLang.Op) (a : List Value)
    (r : ClosSem.State (NumSet × C) F) (g : State) (allowed : Nat → Prop)
    (t : ClosSem.State C F) (v : List Value) :
    match doApp op a.reverse r with
    | .err (.raise _) => False
    | .err (.abort e) => e = .typeError ∨ ∃ event, e = .ffiError event ∧
        (List.Forall₂ (valueRel g allowed t.code) a v ∧ stateRel g allowed r t →
          doApp op v.reverse t = .err (.abort (.ffiError event)))
    | .val (w, s) =>
        (stateValuesWellFormed g allowed t.code r ∧
          (∀ x ∈ a, valueWellFormed g allowed t.code x) →
            stateValuesWellFormed g allowed t.code s ∧ valueWellFormed g allowed t.code w) ∧
        (List.Forall₂ (valueRel g allowed t.code) a v ∧ stateRel g allowed r t →
          ∃ w' s', doApp op v.reverse t = .val (w', s') ∧
            valueRel g allowed t.code w w' ∧ stateRel g allowed s s') := by
  cases run : doApp op a.reverse r with
  | err error =>
    have shape := doApp_error_shape op a.reverse r error run
    cases error with
    | raise value => simp at shape
    | abort e =>
      cases e with
      | typeError => simp
      | timeoutError => simp at shape
      | ffiError event =>
        right
        refine ⟨event, rfl, ?_⟩
        rintro ⟨valuesRel, statesRel⟩
        have simulated := ClosProps.PrimitiveTotal.simpleValRelDoApp (valueRel g allowed t.code)
          (fun (s : ClosSem.State (NumSet × C) F) (u : ClosSem.State C F) =>
            stateRel g allowed s u ∧ u.code = t.code)
          r t a.reverse v.reverse op
          ⟨valueRel_simple g allowed t.code, stateRel_simple g allowed t.code⟩
          ⟨⟨statesRel, rfl⟩, List.rel_reverse valuesRel⟩
        rw [run] at simulated
        obtain ⟨err, target, relation⟩ := simulated
        cases err <;> simp_all [excRel]
  | val output =>
    obtain ⟨w, s⟩ := output
    constructor
    · rintro ⟨stateSafe, valuesSafe⟩
      have listSafe : List.Forall₂ (fun x y => valueWellFormed g allowed t.code x ∧ x = y) a a := by
        clear run
        induction a with
        | nil => exact .nil
        | cons x xs ih =>
          apply List.Forall₂.cons
          · exact ⟨valuesSafe x (by simp), rfl⟩
          · apply ih
            intro x member
            exact valuesSafe x (by simp [member])
      have simulated := ClosProps.PrimitiveTotal.simpleValRelDoApp
        (fun x y => valueWellFormed g allowed t.code x ∧ x = y)
        (fun (s u : ClosSem.State (NumSet × C) F) =>
          stateValuesWellFormed g allowed t.code s ∧ s = u)
        r r a.reverse a.reverse op
        ⟨valueWellFormed_simple g allowed t.code, stateValuesWellFormed_simple g allowed t.code⟩
        ⟨⟨stateSafe, rfl⟩, List.rel_reverse listSafe⟩
      rw [run] at simulated
      obtain ⟨w', s', ⟨valueSafe, _⟩, ⟨nextSafe, _⟩, _⟩ := simulated
      exact ⟨nextSafe, valueSafe⟩
    · rintro ⟨valuesRel, statesRel⟩
      have simulated := ClosProps.PrimitiveTotal.simpleValRelDoApp (valueRel g allowed t.code)
        (fun (s : ClosSem.State (NumSet × C) F) (u : ClosSem.State C F) =>
          stateRel g allowed s u ∧ u.code = t.code)
        r t a.reverse v.reverse op
        ⟨valueRel_simple g allowed t.code, stateRel_simple g allowed t.code⟩
        ⟨⟨statesRel, rfl⟩, List.rel_reverse valuesRel⟩
      rw [run] at simulated
      obtain ⟨w', s', values, ⟨states, _⟩, target⟩ := simulated
      exact ⟨w', s', target, values, states⟩

end Flapjack.Compiler.Backend.ClosCall
