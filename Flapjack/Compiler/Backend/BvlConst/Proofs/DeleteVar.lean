import Flapjack.Compiler.Backend.BvlConst.Proofs.Relations
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Semantic prerequisites for deleting let-bound variable aliases. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

namespace DeleteVarListCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end DeleteVarListCarrier

/-- A successfully evaluated singleton still succeeds after variable deletion
and leaves the same state, though its value may change. This helper has no
standalone HOL declaration. -/
theorem evaluate_deleteVar_success {C F : Type} (expression : Bvl.Exp)
    (state next : State C F) (env : List Value) (values : List Value)
    (run : evaluate [expression] env state = (.val values, next)) :
    ∃ output, evaluate [BvlConst.deleteVar expression] env state = (.val output, next) := by
  cases expression with
  | var index =>
    cases lookup : env[index]? with
    | none => simp [evaluate, lookup] at run
    | some value =>
      simp [evaluate, lookup] at run
      obtain ⟨_, rfl⟩ := run
      refine ⟨[.number 0], ?_⟩
      change evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state)
      simp [evaluate, fixClock, doApp, applyNumeric, doIntApp]
  | _ => exact ⟨values, by simpa [BvlConst.deleteVar] using run⟩

/-- Deleting variable aliases in an expression list preserves a non-type-error
result and its final state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "evaluate_delete_var_Rerr"
  (fmap_as_finite_support := [refs])]
theorem evaluate_deleteVar_list_error {C F : Type} (expressions : List Bvl.Exp)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F) (env : List Value)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (run : evaluateTuple (expressions, env, state) = (.err error, final))
    (notTypeError : error ≠ .abort .typeError) :
    evaluateTuple (expressions.map BvlConst.deleteVar, env, state) = (.err error, final) := by
  induction expressions generalizing state with
  | nil => simp [evaluateTuple, evaluate] at run
  | cons head tail ih =>
    rw [evaluateCons] at run
    simp only [List.map_cons]
    rw [evaluateCons]
    cases headRun : evaluateTuple ([head], env, state) with
    | mk headResult next =>
      cases headResult with
      | err headError =>
        simp [headRun] at run
        rcases run with ⟨rfl, rfl⟩
        rw [evaluate_deleteVar_error head state next headError env headRun notTypeError]
      | val values =>
        have headRun' : evaluate [head] env state = (.val values, next) := headRun
        obtain ⟨output, transformedHead⟩ := evaluate_deleteVar_success head state next env values headRun'
        change evaluateTuple ([BvlConst.deleteVar head], env, state) = (.val output, next) at transformedHead
        simp only [headRun] at run
        rw [transformedHead]
        cases tailRun : evaluateTuple (tail, env, next) with
        | mk tailResult last =>
          cases tailResult with
          | val tailValues => simp [tailRun] at run
          | err tailError =>
            simp [tailRun] at run
            rcases run with ⟨rfl, rfl⟩
            dsimp only
            rw [ih next tailRun]

end Flapjack.Compiler.Backend.BvlConst.Proofs
