module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileLetCase
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

@[expose] public section

/-! Evaluation of variable-only argument lists for auxiliary calls. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value State evaluate evaluateTuple)
open Flapjack.Compiler.Backend.BvlProps (isVar bVarBound evaluateCons)

/-- Compiling a variable-only list preserves its variables and emits no
auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_exps_Var_list"]
theorem compileExps_varList (expressions : List Bvl.Exp) (n : Nat)
    (onlyVars : expressions.all isVar = true) :
    ∃ aux : AppList (Nat × Nat × Bvi.Exp),
      compileListSource n expressions =
        (expressions.map (fun exp => Bvi.Exp.var (BvlProps.destVar exp)), aux, n) ∧
      appListAppend aux = [] := by
  induction expressions generalizing n with
  | nil => exact ⟨.nil, by simp [compileListSource, appListAppend, appendAux]⟩
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at onlyVars
    cases head with
    | var index =>
      obtain ⟨aux, compiled, empty⟩ := ih n onlyVars.2
      refine ⟨aux, ?_, empty⟩
      simp [compileListSource, compileSingSource, compiled, BvlProps.destVar, smartAppend]
    | _ => simp [isVar] at onlyVars


namespace VarMapCarrier
/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end VarMapCarrier

/-- Bounded variables evaluate identically with or without a trailing environment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "evaluate_MAP_Var2"
  (fmap_as_finite_support := [refs])]
theorem evaluate_varMapBound {C F : Type} (args : List Bvl.Exp) (vs env : List Value)
    (state : BviSem.BviState C F)
    (premises : bVarBound vs.length args ∧ args.all isVar = true) :
    ∃ ts, BviSem.evaluate (args.map (fun e => Bvi.Exp.var (BvlProps.destVar e))) (vs ++ env) state = (.val ts, state) ∧
      BviSem.evaluate (args.map (fun e => Bvi.Exp.var (BvlProps.destVar e))) vs state = (.val ts, state) := by
  induction args with
  | nil => exact ⟨[], by simp [BviSem.evaluate]⟩
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at premises
    cases head with
    | var index =>
      have headBound : index < vs.length := by
        cases tail with
        | nil => simpa [bVarBound] using premises.1
        | cons a as =>
          have h : index < vs.length ∧ bVarBound vs.length (a :: as) := by
            simpa only [bVarBound] using premises.1
          exact h.1
      have tailBound : bVarBound vs.length tail := by
        cases tail with
        | nil => simp [bVarBound]
        | cons a as =>
          have h : index < vs.length ∧ bVarBound vs.length (a :: as) := by
            simpa only [bVarBound] using premises.1
          exact h.2
      obtain ⟨ts, left, right⟩ := ih ⟨tailBound, premises.2.2⟩
      have lookup : vs[index]? = some vs[index] := by simp [headBound]
      have lookupAppend : (vs ++ env)[index]? = some vs[index] := by
        simp [List.getElem?_append_left headBound, lookup]
      refine ⟨vs[index] :: ts, ?_, ?_⟩
      · simp only [List.map_cons, BvlProps.destVar_var]
        change BviSem.evaluateTuple (_ :: _, _, _) = _
        rw [BviSem.evaluateCons]
        simp [BviSem.evaluateTuple, BviSem.evaluate, lookupAppend, left, Flapjack.holHd]
      · simp only [List.map_cons, BvlProps.destVar_var]
        change BviSem.evaluateTuple (_ :: _, _, _) = _
        rw [BviSem.evaluateCons]
        simp [BviSem.evaluateTuple, BviSem.evaluate, lookup, right, Flapjack.holHd]
    | _ => simp [isVar] at premises

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

/-- A variable-only list can fail only with a type error, without changing
the state. This helper supports the empty-let and handler simulations. -/
theorem evaluate_varList_error {C F : Type} (expressions : List Bvl.Exp)
    (env : List Value) (state final : State C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (onlyVars : expressions.all isVar = true)
    (run : evaluateTuple (expressions, env, state) = (.err error, final)) :
    error = .abort .typeError ∧ state = final := by
  induction expressions generalizing state with
  | nil => simp [evaluateTuple, evaluate] at run
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at onlyVars
    cases head with
    | var index =>
      rw [evaluateCons] at run
      cases lookup : env[index]? with
      | none => simpa [evaluateTuple, evaluate, lookup, eq_comm] using run
      | some value =>
        simp only [evaluateTuple, evaluate, lookup] at run
        cases tailRun : evaluate tail env state with
        | mk tailResult next =>
          cases tailResult with
          | val values => simp [tailRun] at run
          | err tailError =>
            simp [tailRun] at run
            rcases run with ⟨rfl, rfl⟩
            exact ih state onlyVars.2 tailRun
    | _ => simp [isVar] at onlyVars

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
