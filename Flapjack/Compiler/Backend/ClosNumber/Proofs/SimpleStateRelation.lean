module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations

@[expose] public section

/-! Numbering's state relation satisfies the generic primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem ClosProps

namespace SimpleStatePort
/-- The closure state has the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The numbering state relation supports the generic primitive operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "simple_state_rel"
  (fmap_as_finite_support := [refs, code])]
theorem numbering_simpleStateRel {C F : Type} (maxApp : Nat) :
    simpleStateRel (ValueRel maxApp)
      (fun (s : State (Nat × C) F) (t : State C F) => s.maxApp = maxApp ∧ StateRel s t) := by
  simp only [simpleStateRel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, _, rel⟩
    have lookup := rel.2.2.2.2.2.1 ptr
    cases h : s.refs.lookup ptr <;> simp_all [optionRel]
  · intro bytes t s ptr ⟨found, _, rel⟩
    have lookup := rel.2.2.2.2.2.1 ptr
    cases h : s.refs.lookup ptr <;> simp_all [optionRel]
    rename_i ref
    cases ref <;> simp_all [RefRel]
  · intro values t s ptr ⟨found, maxEq, rel⟩
    have lookup := rel.2.2.2.2.2.1 ptr
    cases h : s.refs.lookup ptr <;> simp_all [optionRel]
    rename_i ref
    cases ref <;> simp_all [RefRel]
  · intro mode value t s ptr ⟨found, maxEq, rel⟩
    have lookup := rel.2.2.2.2.2.1 ptr
    cases h : s.refs.lookup ptr <;> simp_all [optionRel]
    rename_i ref
    cases ref <;> simp_all [RefRel]
  · intro s t ⟨maxEq, rel⟩
    refine ⟨rel.2.1, ?_, ?_⟩
    · intro ptr
      have lookup := rel.2.2.2.2.2.1 ptr
      cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;> simp_all [optionRel]
    · simpa [maxEq] using rel.2.2.2.2.2.2.1
  · intro ffi s t ⟨maxEq, rel⟩
    exact ⟨maxEq, stateRel_withFfi ffi rel⟩
  · intro bytes s t ptr ⟨maxEq, rel⟩
    exact ⟨maxEq, stateRel_updateRefs ptr _ _ rel rfl⟩
  · intro s t ptr xs ys ⟨⟨maxEq, rel⟩, values⟩
    exact ⟨maxEq, stateRel_updateRefs ptr _ _ rel (by simpa [RefRel, maxEq] using values)⟩
  · intro s t ptr mode v w ⟨⟨maxEq, rel⟩, values⟩
    exact ⟨maxEq, stateRel_updateRefs ptr _ _ rel ⟨rfl, by simpa [maxEq] using values⟩⟩
  · intro s t xs ys ⟨⟨maxEq, rel⟩, values⟩
    exact ⟨maxEq, stateRel_withGlobals xs ys rel (by simpa [maxEq] using values)⟩
end SimpleStatePort
export SimpleStatePort (numbering_simpleStateRel)
end Flapjack.Compiler.Backend.ClosNumber
