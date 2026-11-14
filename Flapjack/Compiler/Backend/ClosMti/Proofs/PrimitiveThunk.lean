module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluatePrimitive
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

@[expose] public section

/-! Ordinary thunk operations for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

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
  have generic := ClosProps.PrimitiveTotal.simpleValRelDoAppRev
    (ValueRel source.maxApp)
    (fun (s t : State C F) => s.maxApp = source.maxApp ∧ StateRel s t)
    source target left right op
    ⟨simpleValRel source.maxApp, simpleStateRel source.maxApp⟩
    ⟨⟨rfl, premises.1⟩, premises.2⟩
  cases observed : doApp op right target with
  | err error => simpa [observed] using generic
  | val pair =>
    rcases pair with ⟨value, next⟩
    simp only [observed] at generic
    obtain ⟨sourceValue, sourceNext, values, states, run⟩ := generic
    exact ⟨sourceValue, sourceNext, values, states.2, run⟩

/-- Every ordinary operation preserves the clock-bounded simulation. -/
theorem evaluateRel_allOrdinaryWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (targetArgs sourceCode : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode targetArgs) :
    @EvaluateRelWithin C F limit sourceCode [.op trace op targetArgs] :=
  evaluateRel_ordinaryWithin limit trace op targetArgs sourceCode notInstall notForce argsIH
    (fun source target left right states values => doAppLemma source target left right op ⟨states, values⟩)

end Flapjack.Compiler.Backend.ClosMti
