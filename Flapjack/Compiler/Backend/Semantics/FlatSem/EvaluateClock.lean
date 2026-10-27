import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyClock
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Lean.Elab.Tactic.Omega

/-! Clock-preservation prerequisites for flat evaluation. The full mutual
evaluator clock theorem remains open. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- Lifting a primitive result cannot change the evaluator clock. -/
theorem applyResult_clock {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) : (applyResult state op values).1.clock = state.clock := by
  unfold applyResult
  cases run : doApp state op values with
  | none => simp
  | some pair =>
    obtain ⟨next, result⟩ := pair
    have clock := doApp_clock state next op values result run
    cases result <;> simpa using clock

/-- Evaluating a constructor preserves the bound when its argument list does. -/
theorem evaluate_con_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (constructor : Option (FlatLang.CtorId × FlatLang.TypeId))
    (args : List FlatLang.Exp) (argumentClock : (evaluate env state args.reverse).1.clock ≤ state.clock) :
    (evaluate env state [.con trace constructor args]).1.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate env state args.reverse = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result <;> exact argumentClock

/-- Evaluating a raise preserves the bound when its operand does. -/
theorem evaluate_raise_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (operandClock : (evaluate env state [body]).1.clock ≤ state.clock) :
    (evaluate env state [.raise trace body]).1.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate env state [body] = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result <;> exact operandClock

/-- Evaluating a list of at least two expressions preserves the bound when
its tail does after the first result's clock clamp. -/
theorem evaluate_list_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (tailClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate env next (second :: rest)).1.clock ≤ next.clock) :
    (evaluate env state (first :: second :: rest)).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state [first])
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [first]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    have tailBound := Nat.le_trans (tailClock next bound) bound
    generalize tailRun : evaluate env next (second :: rest) = tailResult at *
    obtain ⟨last, result⟩ := tailResult
    cases result <;> exact tailBound

/-- A declaration list preserves the bound when the remaining declarations
do after the first result's clock clamp. -/
theorem evaluate_decs_clock_step {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp)
    (tailClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluateDecs next rest).1.clock ≤ next.clock) :
    (evaluateDecs state (declaration :: rest)).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate ⟨[]⟩ state [declaration])
  rw [evaluateDecs]
  generalize h : fixClock state (evaluate ⟨[]⟩ state [declaration]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    have tailBound := Nat.le_trans (tailClock next bound) bound
    split <;> assumption

/-- A recursive binding preserves the bound when its body does in the
extended environment. -/
theorem evaluate_letrec_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (name : Flapjack.AstHOL.VarN) (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (body : FlatLang.Exp)
    (bodyClock : (evaluate { env with v := buildRecEnv funs env env.v } state [body]).1.clock ≤ state.clock) :
    (evaluate env state [.letrec name funs body]).1.clock ≤ state.clock := by
  rw [evaluate]
  split <;> simp_all

/-- A let binding preserves the bound when its body does for every extended
environment at the clamped intermediate clock. -/
theorem evaluate_let_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (name : Option Flapjack.AstHOL.VarN) (first body : FlatLang.Exp)
    (bodyClock : ∀ (newEnv : Environment Value) (next : State C F), next.clock ≤ state.clock →
      (evaluate newEnv next [body]).1.clock ≤ next.clock) :
    (evaluate env state [.let_ trace name first body]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state [first])
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [first]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values => exact Nat.le_trans (bodyClock _ next bound) bound

/-- A conditional preserves the bound when either selected branch does at the
clamped intermediate clock. -/
theorem evaluate_if_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (cond yes no : FlatLang.Exp)
    (yesClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate env next [yes]).1.clock ≤ next.clock)
    (noClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate env next [no]).1.clock ≤ next.clock) :
    (evaluate env state [.if_ trace cond yes no]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state [cond])
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [cond]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · exact bound
    · rename_i body selected
      have choice := doIf_selected _ yes no body selected
      rcases choice with rfl | rfl
      · exact Nat.le_trans (yesClock next bound) bound
      · exact Nat.le_trans (noClock next bound) bound

/-- Pattern matching preserves the clock bound when every selectable row body
does at the clamped intermediate clock. -/
theorem evaluate_match_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (rowClock : ∀ (next : State C F) (bindings : List (Flapjack.AstHOL.VarN × Value)) (branch : FlatLang.Exp),
      next.clock ≤ state.clock → expWeight branch < rowsWeight rows →
      (evaluate { env with v := bindings ++ env.v } next [branch]).1.clock ≤ next.clock) :
    (evaluate env state [.mat trace body rows]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state [body])
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [body]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · exact bound
    · rename_i bindings branch selected
      have weight := selectRow_weight rows next _ bindExnV bindings branch selected
      exact Nat.le_trans (rowClock next bindings branch bound weight) bound

/-- An exception handler preserves the clock bound when every selectable row
body does at the clamped intermediate clock. -/
theorem evaluate_handle_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (rowClock : ∀ (next : State C F) (bindings : List (Flapjack.AstHOL.VarN × Value)) (branch : FlatLang.Exp),
      next.clock ≤ state.clock → expWeight branch < rowsWeight rows →
      (evaluate { env with v := bindings ++ env.v } next [branch]).1.clock ≤ next.clock) :
    (evaluate env state [.handle trace body rows]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state [body])
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [body]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | val values => exact bound
  | err error =>
    cases error with
    | abort error => exact bound
    | raise value =>
      dsimp only
      split
      · exact bound
      · rename_i bindings branch selected
        have weight := selectRow_weight rows next value value bindings branch selected
        exact Nat.le_trans (rowClock next bindings branch bound weight) bound

/-- Flat-specific applications cannot increase the clock, regardless of the
outcome of evaluating their arguments. -/
theorem evaluate_flatApp_clock {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (flatOp : ∀ source, op ≠ .src source) :
    (evaluate env state [.app trace op args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases op with
    | src source => exact (flatOp source rfl).elim
    | globalVarAlloc n => simpa [applyResult_clock] using bound
    | globalVarInit n => simpa [applyResult_clock] using bound
    | globalVarLookup n => simpa [applyResult_clock] using bound
    | tagLenEq tag length => simpa [applyResult_clock] using bound
    | lenEq length => simpa [applyResult_clock] using bound
    | el n => simpa [applyResult_clock] using bound
    | id => simpa [applyResult_clock] using bound

/-- Source primitive applications other than calls, dynamic evaluation, and
thunk forcing cannot increase the clock. -/
theorem evaluate_simpleSourceApp_clock {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : Flapjack.AstHOL.Op) (args : List FlatLang.Exp)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk) :
    (evaluate env state [.app trace (.src op) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => exact bound
  | val values =>
    cases op <;> simp_all [applyResult_clock]

/-- A function application preserves the incoming clock bound when recursive
evaluations at smaller clocks do. This is an induction step for the full
clock theorem, not the full theorem itself. -/
theorem evaluate_call_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (smallerClock : ∀ (newEnv : Environment Value) (newState : State C F) (body : FlatLang.Exp),
      newState.clock < state.clock → (evaluate newEnv newState [body]).1.clock ≤ newState.clock) :
    (evaluate env state [.app trace (.src .opapp) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases call : doOpApp values.reverse with
    | none => simpa [call] using bound
    | some pair =>
      obtain ⟨newEnv, body⟩ := pair
      by_cases zero : next.clock = 0
      · simp [call, zero]
      · have decrease : (decClock next).clock < state.clock := by
          simp only [decClock]
          omega
        have recursive := smallerClock newEnv (decClock next) body decrease
        have resultBound : (evaluate newEnv (decClock next) [body]).1.clock ≤ state.clock := by
          exact Nat.le_trans recursive (Nat.le_of_lt decrease)
        simpa [call, zero] using resultBound

/-- Dynamic evaluation preserves the incoming clock bound when declaration
evaluation at smaller clocks does. -/
theorem evaluate_eval_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (smallerClock : ∀ (newState : State C F) (decs : List FlatLang.Exp),
      newState.clock < state.clock → (evaluateDecs newState decs).1.clock ≤ newState.clock) :
    (evaluate env state [.app trace (.src .eval) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases decoded : doEval values.reverse next.evalConfig with
    | none => simpa [decoded] using bound
    | some payload =>
      obtain ⟨decs, config, returnValue⟩ := payload
      by_cases zero : next.clock = 0
      · simp [decoded, zero]
      · have decrease : (decClock { next with evalConfig := config }).clock < state.clock := by
          simp only [decClock]
          omega
        have recursive := smallerClock (decClock { next with evalConfig := config }) decs decrease
        have resultBound : (evaluateDecs (decClock { next with evalConfig := config }) decs).1.clock ≤ state.clock :=
          Nat.le_trans recursive (Nat.le_of_lt decrease)
        cases result : (evaluateDecs (decClock { next with evalConfig := config }) decs).2 <;>
          simpa [decoded, zero, result] using resultBound

/-- Thunk forcing preserves the clock bound when its generated application
does. The generated application has smaller expression weight. -/
theorem evaluate_force_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (forceBodyClock : ∀ (next : State C F) (value : Value), next.clock ≤ state.clock →
      (evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ next
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))]).1.clock ≤ next.clock) :
    (evaluate env state [.app trace (.src (.thunkOp .forceThunk)) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases thunk : destThunk values next.refs with
    | badRef => simpa [thunk] using bound
    | notThunk => simpa [thunk] using bound
    | isThunk mode value =>
      cases mode with
      | evaluated => simpa [thunk] using bound
      | notEvaluated =>
        have recursive := forceBodyClock next value bound
        have resultBound := Nat.le_trans recursive bound
        generalize bodyRun : evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ next
          [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))] = output at *
        obtain ⟨last, output⟩ := output
        change last.clock ≤ state.clock at resultBound
        cases output with
        | err error => simpa [thunk, bodyRun] using resultBound
        | val newValues =>
          cases updated : updateThunk values last.refs newValues with
          | none => simpa [thunk, bodyRun, updated] using resultBound
          | some refs => simpa [thunk, bodyRun, updated] using resultBound

/-- Clock preservation for expressions and declaration lists, proved by
explicit nested strong induction on clock and expression weight. This is
untagged until the underlying flat evaluator has completed HOL review. -/
theorem evaluate_clock_mutual {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp),
      (evaluate env state expressions).1.clock ≤ state.clock) ∧
    (∀ (state : State C F) (declarations : List FlatLang.Exp),
      (evaluateDecs state declarations).1.clock ≤ state.clock) := by
  have allRanks : ∀ clock weight : Nat,
      (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp),
        state.clock = clock → expsWeight expressions = weight →
        (evaluate env state expressions).1.clock ≤ state.clock) ∧
      (∀ (state : State C F) (declarations : List FlatLang.Exp),
        state.clock = clock → expsWeight declarations + 1 = weight →
        (evaluateDecs state declarations).1.clock ≤ state.clock) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp),
            state.clock ≤ clock → expsWeight expressions < weight →
            (evaluate env state expressions).1.clock ≤ state.clock := by
          intro env state expressions clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact ((clockIH state.clock clockLt) (expsWeight expressions)).1 env state expressions rfl rfl
          · exact (weightIH (expsWeight expressions) weightLt).1 env state expressions clockEq rfl
        have decIH : ∀ (state : State C F) (declarations : List FlatLang.Exp),
            state.clock ≤ clock → expsWeight declarations + 1 < weight →
            (evaluateDecs state declarations).1.clock ≤ state.clock := by
          intro state declarations clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact ((clockIH state.clock clockLt) (expsWeight declarations + 1)).2 state declarations rfl rfl
          · exact (weightIH (expsWeight declarations + 1) weightLt).2 state declarations clockEq rfl
        have smallerExpr : ∀ (env : Environment Value) (state : State C F) (body : FlatLang.Exp),
            state.clock < clock → (evaluate env state [body]).1.clock ≤ state.clock := by
          intro env state body clockLt
          exact ((clockIH state.clock clockLt) (expsWeight [body])).1 env state [body] rfl rfl
        have smallerDecs : ∀ (state : State C F) (decs : List FlatLang.Exp),
            state.clock < clock → (evaluateDecs state decs).1.clock ≤ state.clock := by
          intro state decs clockLt
          exact ((clockIH state.clock clockLt) (expsWeight decs + 1)).2 state decs rfl rfl
        constructor
        · intro env state expressions stateClock measure
          cases expressions with
          | nil => simp [evaluate]
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_list_clock_step
              intro next nextBound
              apply exprIH env next (second :: tail) (by omega)
              simp only [expsWeight] at measure ⊢
              omega
            | nil =>
              cases first with
              | lit t l => simp [evaluate]
              | varLocal t n => simp [evaluate]; split <;> simp
              | fn t n b => simp [evaluate]
              | raise t body =>
                apply evaluate_raise_clock_step
                apply exprIH env state [body] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | con t constructor args =>
                apply evaluate_con_clock_step
                apply exprIH env state args.reverse (by omega)
                rw [expsWeight_reverse]
                simp only [expsWeight, expWeight] at measure
                omega
              | letrec name funs body =>
                apply evaluate_letrec_clock_step
                apply exprIH _ state [body] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | let_ t name first body =>
                apply evaluate_let_clock_step
                intro newEnv next nextBound
                apply exprIH newEnv next [body] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | if_ t cond yes no =>
                apply evaluate_if_clock_step
                · intro next nextBound
                  apply exprIH env next [yes] (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro next nextBound
                  apply exprIH env next [no] (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
              | mat t body rows =>
                apply evaluate_match_clock_step
                intro next bindings branch nextBound branchWeight
                apply exprIH _ next [branch] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | handle t body rows =>
                apply evaluate_handle_clock_step
                intro next bindings branch nextBound branchWeight
                apply exprIH _ next [branch] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | app t op args =>
                cases op with
                | src source =>
                  by_cases call : source = .opapp
                  · subst source
                    apply evaluate_call_clock_step
                    intro newEnv next body nextLt
                    exact smallerExpr newEnv next body (by omega)
                  · by_cases eval : source = .eval
                    · subst source
                      apply evaluate_eval_clock_step
                      intro next decs nextLt
                      exact smallerDecs next decs (by omega)
                    · by_cases force : source = .thunkOp .forceThunk
                      · subst source
                        apply evaluate_force_clock_step
                        intro next value nextBound
                        apply exprIH _ next _ (by omega)
                        have forceWeight := appUnit_force_weight t args
                        simp only [expsWeight, expWeight] at measure ⊢
                        simp only [expWeight] at forceWeight
                        omega
                      · exact evaluate_simpleSourceApp_clock env state t source args call eval force
                | globalVarAlloc n => exact evaluate_flatApp_clock env state t _ args (by simp)
                | globalVarInit n => exact evaluate_flatApp_clock env state t _ args (by simp)
                | globalVarLookup n => exact evaluate_flatApp_clock env state t _ args (by simp)
                | tagLenEq n l => exact evaluate_flatApp_clock env state t _ args (by simp)
                | lenEq l => exact evaluate_flatApp_clock env state t _ args (by simp)
                | el n => exact evaluate_flatApp_clock env state t _ args (by simp)
                | id => exact evaluate_flatApp_clock env state t _ args (by simp)
        · intro state declarations stateClock measure
          cases declarations with
          | nil => simp [evaluateDecs]
          | cons declaration rest =>
            apply evaluate_decs_clock_step
            intro next nextBound
            apply decIH next rest (by omega)
            simp only [expsWeight] at measure
            have := expWeight_pos declaration
            omega
  constructor
  · intro env state expressions
    exact (allRanks state.clock (expsWeight expressions)).1 env state expressions rfl rfl
  · intro state declarations
    exact (allRanks state.clock (expsWeight declarations + 1)).2 state declarations rfl rfl

/-- The single-declaration evaluation projection also preserves the clock. -/
theorem evaluateDec_clock {C F : Type} (state : State C F) (declaration : FlatLang.Exp) :
    (evaluateDec state declaration).1.clock ≤ state.clock := by
  have bound := evaluate_clock_mutual.1 ⟨[]⟩ state [declaration]
  unfold evaluateDec
  generalize h : evaluate ⟨[]⟩ state [declaration] = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => exact bound
  | val values => dsimp only; split <;> exact bound

/-- Clock preservation in explicit result-pair form for expressions, single
declarations, and declaration lists. The evaluator remains under HOL review. -/
theorem evaluate_clock_spec {C F : Type} :
    (∀ (env : Environment Value) (state next : State C F) (expressions : List FlatLang.Exp)
      (result : Result (List Value) Value), evaluate env state expressions = (next, result) →
      next.clock ≤ state.clock) ∧
    (∀ (state next : State C F) (declaration : FlatLang.Exp) (result : Option (ErrorResult Value)),
      evaluateDec state declaration = (next, result) → next.clock ≤ state.clock) ∧
    (∀ (state next : State C F) (declarations : List FlatLang.Exp) (result : Option (ErrorResult Value)),
      evaluateDecs state declarations = (next, result) → next.clock ≤ state.clock) := by
  refine ⟨?_, ?_, ?_⟩
  · intro env state next expressions result run
    have bound := evaluate_clock_mutual.1 env state expressions
    simpa [run] using bound
  · intro state next declaration result run
    have bound := evaluateDec_clock state declaration
    simpa [run] using bound
  · intro state next declarations result run
    have bound := evaluate_clock_mutual.2 state declarations
    simpa [run] using bound

/-- Clock clamping is redundant after any expression, declaration, or
declaration-list evaluation in the current clocked evaluator. -/
theorem fixClock_evaluations {C F : Type} (env : Environment Value) (state : State C F)
    (expressions : List FlatLang.Exp) (declaration : FlatLang.Exp) (declarations : List FlatLang.Exp) :
    fixClock state (evaluate env state expressions) = evaluate env state expressions ∧
    fixClock state (evaluateDec state declaration) = evaluateDec state declaration ∧
    fixClock state (evaluateDecs state declarations) = evaluateDecs state declarations := by
  constructor
  · have bound := evaluate_clock_mutual.1 env state expressions
    cases run : evaluate env state expressions with
    | mk next result =>
      have nextBound : next.clock ≤ state.clock := by simpa [run] using bound
      simp [fixClock, Nat.min_eq_right nextBound]

  constructor
  · have bound := evaluateDec_clock state declaration
    cases run : evaluateDec state declaration with
    | mk next result =>
      have nextBound : next.clock ≤ state.clock := by simpa [run] using bound
      simp [fixClock, Nat.min_eq_right nextBound]
  · have bound := evaluate_clock_mutual.2 state declarations
    cases run : evaluateDecs state declarations with
    | mk next result =>
      have nextBound : next.clock ≤ state.clock := by simpa [run] using bound
      simp [fixClock, Nat.min_eq_right nextBound]

/-- The declaration-list evaluator sequences the single-declaration
projection, stopping at the first error. -/
theorem evaluateDecs_cons {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp) :
    evaluateDecs state (declaration :: rest) =
      match evaluateDec state declaration with
      | (next, none) => evaluateDecs next rest
      | (next, some error) => (next, some error) := by
  rw [evaluateDecs]
  have unclamped := (fixClock_evaluations ⟨[]⟩ state [declaration] declaration rest).1
  rw [unclamped]
  unfold evaluateDec
  generalize h : evaluate ⟨[]⟩ state [declaration] = evaluated
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => rfl
  | val values => dsimp only; split <;> rfl

end Flapjack.Compiler.Backend.FlatSem
