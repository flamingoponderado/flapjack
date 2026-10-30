import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileLetCase
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Evaluation of variable-only argument lists for auxiliary calls. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value State evaluate evaluateTuple)
open Flapjack.Compiler.Backend.BvlProps (isVar evaluateCons)

/-- Successful variable-only evaluation leaves the state unchanged and
returns only values already in the environment. Untagged pending source
statement and carrier review. -/
theorem evaluate_varList_members {C F : Type} (expressions : List Bvl.Exp)
    (env : List Value) (state final : State C F) (values : List Value)
    (onlyVars : expressions.all isVar = true)
    (run : evaluateTuple (expressions, env, state) = (.val values, final)) :
    (∀ value ∈ values, value ∈ env) ∧ state = final := by
  induction expressions generalizing state values with
  | nil =>
    simp [evaluateTuple, evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    simp
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at onlyVars
    cases head with
    | var index =>
      rw [evaluateCons] at run
      cases lookup : env[index]? with
      | none => simp [evaluateTuple, evaluate, lookup] at run
      | some value =>
        simp only [evaluateTuple, evaluate, lookup] at run
        cases tailRun : evaluate tail env state with
        | mk tailResult next =>
          cases tailResult with
          | err error => simp [tailRun] at run
          | val tailValues =>
            simp [tailRun, Flapjack.holHd] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨members, unchanged⟩ := ih state tailValues onlyVars.2 tailRun
            constructor
            · intro v member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact List.mem_of_getElem? lookup
              · exact members v member
            · exact unchanged
    | _ => simp [isVar] at onlyVars

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
