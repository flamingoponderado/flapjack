module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.SimpleStateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

@[expose] public section

/-! Primitive-operation simulation for closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.SemanticPrimitivesProps

namespace PrimitivePort
/-- The closure state has the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- A primitive step preserves the fixed maximum application and state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "do_app_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem do_app_lemma {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (xs ys : List Value) (op : ClosLang.Op)
    (h : StateRel source target ∧ List.Forall₂ (ValueRel source.maxApp) xs ys) :
    match doApp op xs source with
    | .val (x, sourceNext) => ∃ y targetNext,
        ValueRel source.maxApp x y ∧
        (sourceNext.maxApp = source.maxApp ∧ StateRel sourceNext targetNext) ∧
        doApp op ys target = .val (y, targetNext)
    | .err error => ∃ targetError,
        doApp op ys target = .err targetError ∧ excRel (ValueRel source.maxApp) error targetError := by
  have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp (ValueRel source.maxApp)
    (fun (s : State (Nat × C) F) (t : State C F) => s.maxApp = source.maxApp ∧ StateRel s t)
    source target xs ys op ⟨simpleValRel source.maxApp, numbering_simpleStateRel source.maxApp⟩
    ⟨⟨rfl, h.1⟩, h.2⟩
  cases run : doApp op xs source <;> simpa only [run] using sim
end PrimitivePort
end Flapjack.Compiler.Backend.ClosNumber
