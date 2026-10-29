import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock

/-! Successful-result length properties for the clocked flat evaluator.
The evaluator remains pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- A successful primitive application returns one value. -/
theorem applyResult_length {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (arguments values : List Value) (run : applyResult state op arguments = (next, .val values)) :
    values.length = 1 := by
  unfold applyResult at run
  cases applied : doApp state op arguments with
  | none => simp [applied] at run
  | some pair =>
    obtain ⟨next', result⟩ := pair
    cases result <;> simp_all
    rcases run with ⟨_, rfl⟩
    rfl


/-- Successful literal, variable and closure evaluations return one value. -/
theorem evaluate_atom_length {C F : Type} (env : Environment Value) (state next : State C F)
    (expression : FlatLang.Exp) (values : List Value)
    (atom : (∃ trace lit, expression = .lit trace lit) ∨
      (∃ trace name, expression = .varLocal trace name) ∨
      (∃ trace name body, expression = .fn trace name body))
    (run : evaluate env state [expression] = (next, .val values)) : values.length = 1 := by
  rcases atom with ⟨trace, lit, rfl⟩ | ⟨trace, name, rfl⟩ | ⟨trace, name, body, rfl⟩
  · simp [evaluate] at run; simp [← run.2]
  · simp only [evaluate] at run
    split at run <;> simp_all
    rcases run with ⟨_, rfl⟩
    rfl
  · simp [evaluate] at run; simp [← run.2]

/-- A successful constructor evaluation returns exactly one constructor. -/
theorem evaluate_con_length {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (tag : Option (FlatLang.CtorId × FlatLang.TypeId))
    (arguments : List FlatLang.Exp) (values : List Value)
    (run : evaluate env state [.con trace tag arguments] = (next, .val values)) : values.length = 1 := by
  simp only [evaluate] at run
  split at run <;> simp_all
  rcases run with ⟨_, rfl⟩
  rfl

/-- A raise expression cannot produce a successful value result. -/
theorem evaluate_raise_noValue {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (values : List Value)
    (run : evaluate env state [.raise trace body] = (next, .val values)) : False := by
  simp only [evaluate] at run
  split at run <;> simp_all

/-- A let expression returns one value if its body does. -/
theorem evaluate_let_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (name : Option VarN) (first body : FlatLang.Exp) (values : List Value)
    (bodyIH : ∀ (newEnv : Environment Value) (newState final : State C F) result,
      newState.clock ≤ state.clock → evaluate newEnv newState [body] = (final, .val result) → result.length = 1)
    (run : evaluate env state [.let_ trace name first body] = (next, .val values)) : values.length = 1 := by
  have bound := fixClock_clock_le state (evaluate env state [first])
  simp only [evaluate] at run
  split at run
  · simp_all
  · exact bodyIH _ _ next values bound run

/-- A recursive binding returns one value if its body does. -/
theorem evaluate_letrec_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : VarN) (funs : List (VarN × VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (values : List Value)
    (bodyIH : ∀ newEnv final result, evaluate newEnv state [body] = (final, .val result) → result.length = 1)
    (run : evaluate env state [.letrec trace funs body] = (next, .val values)) : values.length = 1 := by
  simp only [evaluate] at run
  split at run
  · exact bodyIH _ next values run
  · simp_all

/-- A conditional returns one value if both branches do. -/
theorem evaluate_if_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (condition yes no : FlatLang.Exp) (values : List Value)
    (yesIH : ∀ (newState final : State C F) result, newState.clock ≤ state.clock → evaluate env newState [yes] = (final, .val result) → result.length = 1)
    (noIH : ∀ (newState final : State C F) result, newState.clock ≤ state.clock → evaluate env newState [no] = (final, .val result) → result.length = 1)
    (run : evaluate env state [.if_ trace condition yes no] = (next, .val values)) : values.length = 1 := by
  have bound := fixClock_clock_le state (evaluate env state [condition])
  simp only [evaluate] at run
  split at run
  · simp_all
  · split at run
    · simp_all
    · rename_i branch selected
      have choice := doIf_selected _ yes no branch selected
      rcases choice with rfl | rfl
      · exact yesIH _ next values bound run
      · exact noIH _ next values bound run

/-- A match expression returns one value if every selectable row body does. -/
theorem evaluate_mat_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (values : List Value)
    (rowIH : ∀ (newEnv : Environment Value) (newState final : State C F) branch result, newState.clock ≤ state.clock →
      expWeight branch < rowsWeight rows → evaluate newEnv newState [branch] = (final, .val result) → result.length = 1)
    (run : evaluate env state [.mat trace body rows] = (next, .val values)) : values.length = 1 := by
  have bound := fixClock_clock_le state (evaluate env state [body])
  simp only [evaluate] at run
  split at run
  · simp_all
  · split at run
    · simp_all
    · rename_i bindings branch selected
      have weight := selectRow_weight rows _ _ bindExnV bindings branch selected
      exact rowIH _ _ next branch values bound weight run

/-- A handler returns one value if its protected expression and every
selectable handler body do. -/
theorem evaluate_handle_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (values : List Value)
    (bodyIH : ∀ final result, evaluate env state [body] = (final, .val result) → result.length = 1)
    (rowIH : ∀ (newEnv : Environment Value) (newState final : State C F) branch result, newState.clock ≤ state.clock →
      expWeight branch < rowsWeight rows → evaluate newEnv newState [branch] = (final, .val result) → result.length = 1)
    (run : evaluate env state [.handle trace body rows] = (next, .val values)) : values.length = 1 := by
  have bound := fixClock_clock_le state (evaluate env state [body])
  simp only [evaluate] at run
  split at run
  · split at run
    · simp_all
    · rename_i bindings branch selected
      have weight := selectRow_weight rows _ _ _ bindings branch selected
      exact rowIH _ _ next branch values bound weight run
  · have valueRun : (evaluate env state [body]).2 = .val values := by
      cases h : evaluate env state [body] with
      | mk intermediate result => cases result <;> simp_all [fixClock]
    have actualRun : evaluate env state [body] = ((evaluate env state [body]).1, .val values) :=
      Prod.ext rfl valueRun
    exact bodyIH _ values actualRun

/-- Flat-specific primitive applications return a singleton on success. -/
theorem evaluate_flatApp_length {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp) (values : List Value)
    (flatOp : ∀ source, op ≠ .src source)
    (run : evaluate env state [.app trace op args] = (next, .val values)) : values.length = 1 := by
  rw [evaluate] at run
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at run
  obtain ⟨intermediate, result⟩ := evaluated
  cases result with
  | err error => simp at run
  | val argsValues =>
    cases op with
    | src source => exact (flatOp source rfl).elim
    | globalVarAlloc n => exact applyResult_length _ _ _ _ _ run
    | globalVarInit n => exact applyResult_length _ _ _ _ _ run
    | globalVarLookup n => exact applyResult_length _ _ _ _ _ run
    | tagLenEq tag length => exact applyResult_length _ _ _ _ _ run
    | lenEq length => exact applyResult_length _ _ _ _ _ run
    | el n => exact applyResult_length _ _ _ _ _ run
    | id => exact applyResult_length _ _ _ _ _ run

/-- Non-recursive source primitive applications return a singleton on success. -/
theorem evaluate_simpleSourceApp_length {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (op : Op) (args : List FlatLang.Exp) (values : List Value)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk)
    (run : evaluate env state [.app trace (.src op) args] = (next, .val values)) : values.length = 1 := by
  rw [evaluate] at run
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at run
  obtain ⟨intermediate, result⟩ := evaluated
  cases result with
  | err error => simp at run
  | val argsValues =>
    cases op <;> simp_all <;> exact applyResult_length _ _ _ _ _ run

/-- Function calls return a singleton if all smaller-clock bodies do. -/
theorem evaluate_call_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp) (values : List Value)
    (bodyIH : ∀ (newEnv : Environment Value) (newState final : State C F) (body : FlatLang.Exp) result,
      newState.clock < state.clock → evaluate newEnv newState [body] = (final, .val result) → result.length = 1)
    (run : evaluate env state [.app trace (.src .opapp) args] = (next, .val values)) : values.length = 1 := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate] at run
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at run bound
  obtain ⟨intermediate, result⟩ := evaluated
  change intermediate.clock ≤ state.clock at bound
  cases result with
  | err error => simp at run
  | val argsValues =>
    cases call : doOpApp argsValues.reverse with
    | none => simp [call] at run
    | some pair =>
      obtain ⟨newEnv, body⟩ := pair
      by_cases zero : intermediate.clock = 0
      · simp [call, zero] at run
      · have decrease : (decClock intermediate).clock < state.clock := by simp only [decClock]; omega
        apply bodyIH newEnv (decClock intermediate) next body values decrease
        simpa [call, zero] using run

/-- Dynamic evaluation returns a singleton on every successful outcome. -/
theorem evaluate_eval_length {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp) (values : List Value)
    (run : evaluate env state [.app trace (.src .eval) args] = (next, .val values)) : values.length = 1 := by
  rw [evaluate] at run
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at run
  obtain ⟨intermediate, result⟩ := evaluated
  cases result with
  | err error => simp at run
  | val argsValues =>
    cases decoded : doEval argsValues.reverse intermediate.evalConfig with
    | none => simp [decoded] at run
    | some payload =>
      obtain ⟨decs, config, returnValue⟩ := payload
      by_cases zero : intermediate.clock = 0
      · simp [decoded, zero] at run
      · cases result : (evaluateDecs (decClock { intermediate with evalConfig := config }) decs).2 <;>
          simp_all
        rcases run with ⟨_, rfl⟩
        rfl

/-- Thunk forcing returns a singleton when its generated call does. -/
theorem evaluate_force_length_step {C F : Type} (env : Environment Value) (state next : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp) (values : List Value)
    (bodyIH : ∀ (newState final : State C F) (value : Value) result, newState.clock ≤ state.clock →
      evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ newState
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))] = (final, .val result) →
      result.length = 1)
    (run : evaluate env state [.app trace (.src (.thunkOp .forceThunk)) args] = (next, .val values)) :
    values.length = 1 := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate] at run
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at run bound
  obtain ⟨intermediate, result⟩ := evaluated
  change intermediate.clock ≤ state.clock at bound
  cases result with
  | err error => simp at run
  | val argsValues =>
    cases thunk : destThunk argsValues intermediate.refs with
    | badRef => simp [thunk] at run
    | notThunk => simp [thunk] at run
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp [thunk] at run
        rcases run with ⟨_, rfl⟩
        rfl
      | notEvaluated =>
        cases bodyRun : evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ intermediate
            [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))] with
        | mk last output =>
          cases output with
          | err error => simp [thunk, bodyRun] at run
          | val result =>
            cases updated : updateThunk argsValues last.refs result with
            | none => simp [thunk, bodyRun, updated] at run
            | some refs =>
              simp [thunk, bodyRun, updated] at run
              rcases run with ⟨_, rfl⟩
              exact bodyIH intermediate last value result bound bodyRun

/-- A successful singleton evaluation returns exactly one value. The clocked
evaluator and this theorem remain pending HOL correspondence review. -/
theorem evaluate_singleton_length {C F : Type} (env : Environment Value) (state next : State C F)
    (expression : FlatLang.Exp) (values : List Value)
    (run : evaluate env state [expression] = (next, .val values)) : values.length = 1 := by
  have allRanks : ∀ clock weight : Nat,
      ∀ (env : Environment Value) (state next : State C F) (expression : FlatLang.Exp) (values : List Value),
        state.clock = clock → expWeight expression = weight →
        evaluate env state [expression] = (next, .val values) → values.length = 1 := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (env : Environment Value) (state next : State C F) (expression : FlatLang.Exp)
            (values : List Value), state.clock ≤ clock → expWeight expression < weight →
            evaluate env state [expression] = (next, .val values) → values.length = 1 := by
          intro env state next expression values clockLe weightLt run
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expWeight expression) env state next expression values rfl rfl run
          · exact weightIH (expWeight expression) weightLt env state next expression values clockEq rfl run
        intro env state next expression values clockEq weightEq run
        cases expression with
        | lit trace lit => exact evaluate_atom_length env state next _ values (Or.inl ⟨trace, lit, rfl⟩) run
        | varLocal trace name => exact evaluate_atom_length env state next _ values (Or.inr (Or.inl ⟨trace, name, rfl⟩)) run
        | fn trace name body => exact evaluate_atom_length env state next _ values (Or.inr (Or.inr ⟨trace, name, body, rfl⟩)) run
        | raise trace body => exact (evaluate_raise_noValue env state next trace body values run).elim
        | con trace tag args => exact evaluate_con_length env state next trace tag args values run
        | letrec name funs body =>
          apply evaluate_letrec_length_step env state next name funs body values ?_ run
          intro newEnv final result bodyRun
          apply exprIH newEnv state final body result (by omega)
          · simp only [expWeight] at weightEq
            omega
          · exact bodyRun
        | let_ trace name first body =>
          apply evaluate_let_length_step env state next trace name first body values ?_ run
          intro newEnv newState final result nextBound bodyRun
          apply exprIH newEnv newState final body result (by omega)
          · simp only [expWeight] at weightEq
            omega
          · exact bodyRun
        | if_ trace condition yes no =>
          apply evaluate_if_length_step env state next trace condition yes no values ?_ ?_ run
          · intro newState final result nextBound bodyRun
            apply exprIH env newState final yes result (by omega)
            · simp only [expWeight] at weightEq
              omega
            · exact bodyRun
          · intro newState final result nextBound bodyRun
            apply exprIH env newState final no result (by omega)
            · simp only [expWeight] at weightEq
              omega
            · exact bodyRun
        | mat trace body rows =>
          apply evaluate_mat_length_step env state next trace body rows values ?_ run
          intro newEnv newState final branch result nextBound branchWeight branchRun
          apply exprIH newEnv newState final branch result (by omega)
          · simp only [expWeight] at weightEq
            omega
          · exact branchRun
        | handle trace body rows =>
          apply evaluate_handle_length_step env state next trace body rows values ?_ ?_ run
          · intro final result bodyRun
            apply exprIH env state final body result (by omega)
            · simp only [expWeight] at weightEq
              omega
            · exact bodyRun
          · intro newEnv newState final branch result nextBound branchWeight branchRun
            apply exprIH newEnv newState final branch result (by omega)
            · simp only [expWeight] at weightEq
              omega
            · exact branchRun
        | app trace op args =>
          cases op with
          | src source =>
            by_cases call : source = .opapp
            · subst source
              apply evaluate_call_length_step env state next trace args values ?_ run
              intro newEnv newState final body result smaller bodyRun
              exact clockIH newState.clock (by omega) (expWeight body) newEnv newState final body result rfl rfl bodyRun
            · by_cases isEval : source = .eval
              · subst source
                exact evaluate_eval_length env state next trace args values run
              · by_cases force : source = .thunkOp .forceThunk
                · subst source
                  apply evaluate_force_length_step env state next trace args values ?_ run
                  intro newState final value result nextBound bodyRun
                  apply exprIH _ newState final
                    (appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))) result (by omega)
                  · have smaller := appUnit_force_weight trace args
                    omega
                  · exact bodyRun
                · exact evaluate_simpleSourceApp_length env state next trace source args values call isEval force run
          | globalVarAlloc id => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
          | globalVarInit id => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
          | globalVarLookup id => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
          | tagLenEq tag len => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
          | lenEq len => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
          | el index => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
          | id => exact evaluate_flatApp_length env state next trace _ args values (by simp) run
  exact allRanks state.clock (expWeight expression) env state next expression values rfl rfl run

/-- Successful evaluation preserves expression-list length. -/
theorem evaluate_length {C F : Type} (env : Environment Value) (state next : State C F)
    (expressions : List FlatLang.Exp) (values : List Value)
    (run : evaluate env state expressions = (next, .val values)) : values.length = expressions.length := by
  induction expressions generalizing state next values with
  | nil => simp [evaluate] at run; simp [← run.2]
  | cons first rest ih =>
    cases rest with
    | nil => simpa using evaluate_singleton_length env state next first values run
    | cons second rest =>
      simp only [evaluate] at run
      split at run
      · simp_all
      · split at run
        · simp_all
        · rename_i firstValues tailValues tailRun
          have length := ih _ _ tailValues (Prod.ext rfl tailRun)
          rcases run with ⟨_, rfl⟩
          simp [length]

end Flapjack.Compiler.Backend.FlatSem
