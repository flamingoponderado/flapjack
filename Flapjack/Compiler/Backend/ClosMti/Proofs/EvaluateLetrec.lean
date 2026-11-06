import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateCases

/-! Recursive function bindings in the closure introduction simulation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Collecting a unary function yields a related multi-argument function. -/
theorem functionRel_introFun (maxApp : Nat) (function : Nat × ClosLang.Exp)
    (positive : 1 ≤ maxApp) (unary : function.1 = 1 ∧ ClosProps.noMti function.2) :
    FunctionRel maxApp function (introFun maxApp function) := by
  obtain ⟨arity, body⟩ := function
  obtain ⟨rfl, bodyUnary⟩ := unary
  cases collected : collectArgs maxApp 1 body with
  | mk count remaining =>
    have bounds := collectArgsBounds maxApp 1 body count remaining collected positive
    obtain ⟨names, bodyEq, countEq, restUnary⟩ :=
      collectArgsUnary maxApp 1 body count remaining collected bodyUnary
    simp only [introFun, collected]
    refine ⟨remaining, names, ?_, bounds.2, restUnary, rfl, bodyEq, ?_⟩
    · simp [CodeRel, introList, restUnary]
    · simp [countEq, Nat.add_comm]

/-- Every unary recursive function is related to its collected form. -/
theorem functionRel_introFuns (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (positive : 1 ≤ maxApp) (unary : ClosProps.noMtiFuns functions) :
    List.Forall₂ (FunctionRel maxApp) functions (functions.map (introFun maxApp)) := by
  induction functions with
  | nil => exact .nil
  | cons function rest ih =>
    obtain ⟨arity, body⟩ := function
    simp only [ClosProps.noMtiFuns] at unary
    exact .cons (functionRel_introFun maxApp (arity, body) positive ⟨unary.1, unary.2.1⟩) (ih unary.2.2)

/-- The source and transformed recursive function bundles have valid arities. -/
theorem introFuns_valid (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (positive : 1 ≤ maxApp) (unary : ClosProps.noMtiFuns functions) :
    functions.all (fun (arity, _) => arity ≤ maxApp && arity != 0) = true ∧
    (functions.map (introFun maxApp)).all (fun (arity, _) => arity ≤ maxApp && arity != 0) = true := by
  induction functions with
  | nil => simp
  | cons function rest ih =>
    obtain ⟨arity, body⟩ := function
    simp only [ClosProps.noMtiFuns] at unary
    obtain ⟨rfl, bodyUnary, restUnary⟩ := unary
    obtain ⟨sourceValid, targetValid⟩ := ih restUnary
    have rel := functionRel_introFun maxApp (1, body) positive ⟨rfl, bodyUnary⟩
    have targetBounds : (introFun maxApp (1, body)).1 ≤ maxApp ∧
        0 < (introFun maxApp (1, body)).1 := by
      exact ⟨by obtain ⟨_, _, _, bound, _⟩ := rel; exact bound,
        functionRel_target_arity_pos rel⟩
    simp [sourceValid, targetValid, positive, targetBounds.1, Nat.ne_of_gt targetBounds.2]

/-- Related recursive bundles produce pointwise related recursive closures. -/
theorem recursiveClosures_related (maxApp : Nat) (functions targetFunctions : List (Nat × ClosLang.Exp))
    (sourceEnv targetEnv : List Value)
    (functionsRel : List.Forall₂ (FunctionRel maxApp) functions targetFunctions)
    (envRel : List.Forall₂ (ValueRel maxApp) sourceEnv targetEnv) :
    List.Forall₂ (ValueRel maxApp)
      ((List.range functions.length).map (fun i => Value.recclosure none [] sourceEnv functions i))
      ((List.range targetFunctions.length).map (fun i => Value.recclosure none [] targetEnv targetFunctions i)) := by
  have sameLength := functionsRel.length_eq
  rw [sameLength]
  generalize h : List.range targetFunctions.length = indices
  have bounds : ∀ i ∈ indices, i < targetFunctions.length := by
    intro i member
    rw [← h] at member
    simpa using member
  clear h
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    simp only [List.map_cons]
    refine .cons (.recclosure sourceEnv targetEnv functions targetFunctions index
      functionsRel envRel (bounds index (by simp))) ?_
    apply ih
    intro i member
    exact bounds i (by simp [member])

/-- Introduction preserves the outer recursive-binding constructor on
unary source code and collects the function bundle. -/
theorem introExp_eq_letrec (maxApp : Nat) (expression : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString) (location : Option Nat) (vars : Option (List Nat))
    (targetFunctions : List (Nat × ClosLang.Exp)) (targetBody : ClosLang.Exp)
    (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .letrec names location vars targetFunctions targetBody) :
    ∃ functions body, expression = .letrec names none none functions body ∧
      ClosProps.noMtiFuns functions ∧ ClosProps.noMti body ∧ location = none ∧ vars = none ∧
      targetFunctions = functions.map (introFun maxApp) ∧ targetBody = introExp maxApp body := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Recursive bindings preserve a clock-bounded body simulation. -/
theorem evaluateRel_letrecWithin {C F : Type} (limit : Nat) (names : List Basis.Pure.MlString.MlString)
    (location : Option Nat) (vars : Option (List Nat))
    (targetFunctions : List (Nat × ClosLang.Exp)) (targetBody : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode [.letrec names location vars targetFunctions targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression =
          .letrec names location vars targetFunctions targetBody := by
        simpa [introList] using code.2.symm
      obtain ⟨functions, body, rfl, functionsUnary, bodyUnary, rfl, rfl, rfl, bodyEq⟩ :=
        introExp_eq_letrec source.maxApp expression names location vars targetFunctions targetBody unary transformed
      have positive : 1 ≤ source.maxApp := by
        have agreement := stateRel_clock_maxApp states
        omega
      have targetMax : target.maxApp = source.maxApp := (stateRel_clock_maxApp states).2.1.symm
      have functionsRel := functionRel_introFuns source.maxApp functions positive functionsUnary
      have valid := introFuns_valid source.maxApp functions positive functionsUnary
      have targetValid : (functions.map (introFun source.maxApp)).all
          (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
        simpa [targetMax] using valid.2
      have recursiveRel := recursiveClosures_related source.maxApp functions
        (functions.map (introFun source.maxApp)) sourceEnv targetEnv functionsRel env
      have extended : List.Forall₂ (ValueRel source.maxApp)
          (((List.range functions.length).map (fun i => Value.recclosure none [] sourceEnv functions i)) ++ sourceEnv)
          (((List.range (functions.map (introFun source.maxApp)).length).map
            (fun i => Value.recclosure none [] targetEnv (functions.map (introFun source.maxApp)) i)) ++ targetEnv) :=
        List.rel_append recursiveRel env
      have bodyCode : CodeRel source.maxApp [body] [targetBody] := by
        simp [CodeRel, introList, bodyUnary, bodyEq]
      have targetBodyRun : evaluate [targetBody]
          (((List.range (functions.map (introFun source.maxApp)).length).map
            (fun i => Value.recclosure none [] targetEnv (functions.map (introFun source.maxApp)) i)) ++ targetEnv)
          target = (targetResult, targetFinal) := by
        simpa [evaluate, targetValid] using run
      obtain ⟨sourceResult, sourceFinal, sourceBodyRun, bodyRel, finalStates⟩ :=
        bodyIH [body] _ target _ targetFinal source targetResult clock targetBodyRun extended states bodyCode
      refine ⟨sourceResult, sourceFinal, ?_, bodyRel, finalStates⟩
      simpa [evaluate, valid.1] using sourceBodyRun

end Flapjack.Compiler.Backend.ClosMti
