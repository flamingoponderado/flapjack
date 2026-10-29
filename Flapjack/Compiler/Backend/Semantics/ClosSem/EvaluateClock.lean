import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClock

/-! Clock bounds for the proof-side unbounded closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Clamping an evaluation result bounds its clock by the input clock. -/
theorem fixClock_clock_le {C F : Type} (state : State C F) (result : EvalResult C F) :
    (fixClock state result).2.clock ≤ state.clock := by
  exact Nat.min_le_left _ _

/-- A primitive result retains the input clock on success. -/
theorem doApp_success_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (run : doApp op args state = .val (value, next)) : next.clock ≤ state.clock := by
  rw [doApp_clock op args state next value run]

/-- Evaluating a multi-expression list respects the clock bound when the
tail does after the first expression's clock clamp. -/
theorem evaluate_list_clock_step {C F : Type} (env : List Value) (state : State C F)
    (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (tailClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate (second :: rest) env next).2.clock ≤ next.clock) :
    (evaluate (first :: second :: rest) env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate [first] env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate [first] env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    have tailBound := Nat.le_trans (tailClock next bound) bound
    generalize tailRun : evaluate (second :: rest) env next = evaluatedTail at *
    obtain ⟨tailResult, last⟩ := evaluatedTail
    cases tailResult <;> exact tailBound

/-- A raise preserves the clock bound if its operand does. -/
theorem evaluate_raise_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (operandClock : (evaluate [body] env state).2.clock ≤ state.clock) :
    (evaluate [.raise trace body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate [body] env state = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  cases result <;> exact operandClock

/-- A let-expression respects the bound when its body does for every
environment and every clock reached after evaluating the bindings. -/
theorem evaluate_let_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (bodyClock : ∀ (newEnv : List Value) (next : State C F), next.clock ≤ state.clock →
      (evaluate [body] newEnv next).2.clock ≤ next.clock) :
    (evaluate [.let trace bindings body] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate bindings env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate bindings env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values => exact Nat.le_trans (bodyClock (values ++ env) next bound) bound

/-- A handler respects the bound when its handler expression does for each
raised value at the clamped intermediate state. -/
theorem evaluate_handle_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (handlerClock : ∀ (value : Value) (next : State C F), next.clock ≤ state.clock →
      (evaluate [handler] (value :: env) next).2.clock ≤ next.clock) :
    (evaluate [.handle trace body handler] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate [body] env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate [body] env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | val values => exact bound
  | err error =>
    cases error with
    | abort reason => exact bound
    | raise value => exact Nat.le_trans (handlerClock value next bound) bound

/-- A conditional respects the bound when both branches do at the clamped
condition state. -/
theorem evaluate_if_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp)
    (yesClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate [yes] env next).2.clock ≤ next.clock)
    (noClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate [no] env next).2.clock ≤ next.clock) :
    (evaluate [.ifThenElse trace condition yes no] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate [condition] env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate [condition] env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · simpa using bound
    · exact Nat.le_trans (yesClock next bound) bound
    · exact Nat.le_trans (noClock next bound) bound

/-- A recursive binding preserves the bound when its body does in any
extended environment at the original state. -/
theorem evaluate_letrec_clock_step {C F : Type} (env : List Value) (state : State C F)
    (names : List Flapjack.AstHOL.VarN) (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (bodyClock : ∀ newEnv, (evaluate [body] newEnv state).2.clock ≤ state.clock) :
    (evaluate [.letrec names location selected functions body] env state).2.clock ≤ state.clock := by
  rw [evaluate.eq_def]
  dsimp only
  split
  · split
    · simp
    · exact bodyClock _
  · simp

/-- A tick either times out immediately or evaluates its body with a smaller
clock. -/
theorem evaluate_tick_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyClock : (evaluate [body] env (decClock 1 state)).2.clock ≤ (decClock 1 state).clock) :
    (evaluate [.tick trace body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · exact Nat.le_trans bodyClock (Nat.sub_le _ _)

/-- A direct code call preserves the bound when its selected body does at
every smaller clock. -/
theorem evaluate_call_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (ticks location : Nat) (args : List ClosLang.Exp)
    (bodyClock : ∀ (body : ClosLang.Exp) (values : List Value) (next : State C F),
      next.clock < state.clock → (evaluate [body] values next).2.clock ≤ next.clock) :
    (evaluate [.call trace ticks location args] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · simpa using bound
    · rename_i selected body found
      split
      · simp
      · have smaller : (decClock (ticks + 1) next).clock < state.clock := by
          simp only [decClock]
          omega
        exact Nat.le_trans (bodyClock body selected _ smaller) (Nat.le_of_lt smaller)

/-- An application expression preserves the clock bound when applying the
evaluated closure does at every state bounded by the original clock. -/
theorem evaluate_app_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (location : Option Nat) (function : ClosLang.Exp)
    (args : List ClosLang.Exp)
    (appClock : ∀ (function : Value) (values : List Value) (next : State C F),
      next.clock ≤ state.clock → (evaluateApp location function values next).2.clock ≤ next.clock) :
    (evaluate [.app trace location function args] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · have bound := fixClock_clock_le state (evaluate args env state)
    generalize h : fixClock state (evaluate args env state) = evaluated at *
    obtain ⟨result, next⟩ := evaluated
    change next.clock ≤ state.clock at bound
    cases result with
    | err error => exact bound
    | val values =>
      dsimp only
      have secondBound := fixClock_clock_le next (evaluate [function] env next)
      generalize h2 : fixClock next (evaluate [function] env next) = evaluatedFunction at *
      obtain ⟨functionResult, last⟩ := evaluatedFunction
      change last.clock ≤ next.clock at secondBound
      have lastBound := Nat.le_trans secondBound bound
      cases functionResult with
      | err error => exact lastBound
      | val functionValues => exact Nat.le_trans (appClock _ values last lastBound) lastBound

/-- Closure application respects the clock bound when application
evaluations at smaller clocks do. -/
theorem evaluateApp_clock_step {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state : State C F)
    (appClock : ∀ (function : Value) (remaining : List Value) (next : State C F),
      next.clock < state.clock → (evaluateApp location function remaining next).2.clock ≤ next.clock) :
    (evaluateApp location function args state).2.clock ≤ state.clock := by
  cases args with
  | nil => simp [evaluateApp]
  | cons first restArgs =>
    rw [evaluateApp]
    split
    · simp
    · rename_i value selected
      split
      · simp
      · simp [decClock]
    · rename_i body env rest selected
      have consumes := destClosure_full_remaining_lt state.maxApp location function (first :: restArgs)
        env rest body selected
      dsimp only
      split
      · simp
      · rename_i enough
        let start := decClock ((first :: restArgs).length - rest.length) state
        have smaller : start.clock < state.clock := by
          dsimp [start, decClock]
          simp only [List.length_cons] at consumes enough ⊢
          omega
        have bound := fixClock_clock_le start (evaluate [body] env start)
        generalize h : fixClock start (evaluate [body] env start) = evaluated at *
        obtain ⟨result, next⟩ := evaluated
        change next.clock ≤ start.clock at bound
        have nextSmaller : next.clock < state.clock := Nat.lt_of_le_of_lt bound smaller
        cases result with
        | err error => exact Nat.le_of_lt nextSmaller
        | val values =>
          cases values with
          | nil => exact Nat.le_of_lt nextSmaller
          | cons value values =>
            cases values with
            | nil => exact Nat.le_trans (appClock value rest next nextSmaller) (Nat.le_of_lt nextSmaller)
            | cons second values => exact Nat.le_of_lt nextSmaller

/-- Closure application never increases the clock. The proof uses strong
induction on the original clock and does not assume a result or target run. -/
theorem evaluateApp_clock_le {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state : State C F) :
    (evaluateApp location function args state).2.clock ≤ state.clock := by
  have all : ∀ clock : Nat, ∀ (location : Option Nat) (function : Value) (args : List Value)
      (state : State C F), state.clock = clock →
      (evaluateApp location function args state).2.clock ≤ state.clock := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro location function args state stateClock
      apply evaluateApp_clock_step location function args state
      intro value remaining next smaller
      apply ih next.clock (by omega) location value remaining next rfl
  exact all state.clock location function args state rfl

/-- Application expressions cannot increase the clock. -/
theorem evaluate_app_clock_le {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (location : Option Nat) (function : ClosLang.Exp)
    (args : List ClosLang.Exp) :
    (evaluate [.app trace location function args] env state).2.clock ≤ state.clock := by
  apply evaluate_app_clock_step env state trace location function args
  intro value values next _
  exact evaluateApp_clock_le location value values next

/-- Ordinary primitive execution cannot increase the clock. -/
theorem ordinaryOp_clock {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) :
    ((match doApp op values state with
     | .err error => (.err error, state)
     | .val (value, next) => (.val [value], next) : EvalResult C F)).2.clock ≤ state.clock := by
  cases run : doApp op values state with
  | err error => simp
  | val pair =>
    obtain ⟨value, next⟩ := pair
    simpa [run] using doApp_success_clock op values state value next run

/-- An ordinary primitive expression cannot increase the clock. Installation
and forcing have separate evaluation clauses. -/
theorem evaluate_ordinaryOp_clock {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk) :
    (evaluate [.op trace op args] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate.eq_def]
  dsimp only
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases op with
    | install => exact (notInstall rfl).elim
    | thunkOp operation =>
      cases operation with
      | forceThunk => exact (notForce rfl).elim
      | allocThunk mode => exact Nat.le_trans (ordinaryOp_clock (.thunkOp (.allocThunk mode)) values.reverse next) bound
      | updateThunk mode => exact Nat.le_trans (ordinaryOp_clock (.thunkOp (.updateThunk mode)) values.reverse next) bound
    | label n => exact Nat.le_trans (ordinaryOp_clock (.label n) values.reverse next) bound
    | ffi name => exact Nat.le_trans (ordinaryOp_clock (.ffi name) values.reverse next) bound
    | intOp op => exact Nat.le_trans (ordinaryOp_clock (.intOp op) values.reverse next) bound
    | wordOp op => exact Nat.le_trans (ordinaryOp_clock (.wordOp op) values.reverse next) bound
    | blockOp op => exact Nat.le_trans (ordinaryOp_clock (.blockOp op) values.reverse next) bound
    | globOp op => exact Nat.le_trans (ordinaryOp_clock (.globOp op) values.reverse next) bound
    | memOp op => exact Nat.le_trans (ordinaryOp_clock (.memOp op) values.reverse next) bound

/-- Forcing a thunk cannot increase the clock; an unevaluated thunk invokes
the previously bounded closure-application expression. -/
theorem evaluate_force_clock_le {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) :
    (evaluate [.op trace (.thunkOp .forceThunk) args] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    cases inspected : destThunk values next.refs with
    | badRef | notThunk => simpa [inspected] using bound
    | isThunk mode value =>
      cases mode with
      | evaluated => simpa [inspected] using bound
      | notEvaluated =>
        have forceBound := evaluate_app_clock_le [value] next .none none (.var .none 0)
          [.op .none (.blockOp (.cons 0)) []]
        change (evaluate [appUnit (.var .none 0)] [value] next).2.clock ≤ next.clock at forceBound
        generalize forceRun : evaluate [appUnit (.var .none 0)] [value] next = forced at *
        obtain ⟨forcedResult, last⟩ := forced
        have lastBound : last.clock ≤ state.clock := by
          apply Nat.le_trans _ bound
          exact forceBound
        cases forcedResult with
        | err error => simpa [inspected, forceRun] using lastBound
        | val forcedValues =>
          cases update : updateThunk values last.refs forcedValues with
          | none => simpa [inspected, forceRun, update] using lastBound
          | some refs => simpa [inspected, forceRun, update] using lastBound

/-- Dynamic installation preserves the clock bound if the installed code
does at every smaller clock. -/
theorem evaluate_install_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (installedClock : ∀ (program : List ClosLang.Exp) (next : State C F),
      next.clock < state.clock → (evaluate program [] next).2.clock ≤ next.clock) :
    (evaluate [.op trace .install args] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    cases installRun : doInstall values.reverse next with
    | mk installResult installedState =>
      cases installResult with
      | err error =>
        have clock := doInstall_clock_le values.reverse next installedState _ installRun
        simpa [installRun] using Nat.le_trans clock bound
      | val program =>
        have clock := doInstall_success_clock values.reverse next installedState program installRun
        have smaller : installedState.clock < state.clock := by omega
        have programBound := installedClock program installedState smaller
        generalize programRun : evaluate program [] installedState = evaluatedProgram at *
        obtain ⟨programResult, last⟩ := evaluatedProgram
        have lastBound : last.clock ≤ state.clock := Nat.le_trans programBound (Nat.le_of_lt smaller)
        cases programResult <;> simpa [installRun, programRun] using lastBound

/-- The proof-side closure evaluator never increases its clock. The
unbounded evaluator and its carriers remain pending HOL correspondence review. -/
theorem evaluate_clock_le {C F : Type} (expressions : List ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate expressions env state).2.clock ≤ state.clock := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List ClosLang.Exp)
      (env : List Value) (state : State C F), state.clock = clock → expsWeight expressions = weight →
      (evaluate expressions env state).2.clock ≤ state.clock := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state : State C F),
            state.clock ≤ clock → expsWeight expressions < weight →
            (evaluate expressions env state).2.clock ≤ state.clock := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state : State C F),
            state.clock < clock → (evaluate expressions env state).2.clock ≤ state.clock := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => simp [evaluate]
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_list_clock_step
            intro next nextBound
            apply exprIH (second :: tail) env next (by omega)
            simp only [expsWeight] at measure ⊢
            omega
          | nil =>
            cases first with
            | var trace index => simp [evaluate]; split <;> simp
            | fn name location selected arity body =>
              rw [evaluate.eq_def]
              dsimp only
              split <;> simp_all
              split <;> simp_all
            | raise trace body =>
              apply evaluate_raise_clock_step
              apply exprIH [body] env state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | handle trace body handler =>
              apply evaluate_handle_clock_step
              intro value next nextBound
              apply exprIH [handler] (value :: env) next (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | «let» trace bindings body =>
              apply evaluate_let_clock_step
              intro newEnv next nextBound
              apply exprIH [body] newEnv next (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | ifThenElse trace condition yes no =>
              apply evaluate_if_clock_step
              · intro next nextBound
                apply exprIH [yes] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro next nextBound
                apply exprIH [no] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | letrec names location selected functions body =>
              apply evaluate_letrec_clock_step
              intro newEnv
              apply exprIH [body] newEnv state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | tick trace body =>
              apply evaluate_tick_clock_step
              by_cases zero : state.clock = 0
              · apply exprIH [body] env (decClock 1 state) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · apply smaller [body] env (decClock 1 state)
                simp [decClock]
                omega
            | call trace ticks location args =>
              apply evaluate_call_clock_step
              intro body values next nextLt
              exact smaller [body] values next (by omega)
            | app trace location function args => exact evaluate_app_clock_le env state trace location function args
            | op trace op args =>
              cases op with
              | install =>
                apply evaluate_install_clock_step
                intro program next nextLt
                exact smaller program [] next (by omega)
              | thunkOp operation =>
                cases operation with
                | forceThunk => exact evaluate_force_clock_le env state trace args
                | allocThunk mode => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
                | updateThunk mode => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | label n => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | ffi n => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | intOp x => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | wordOp x => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | blockOp x => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | globOp x => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
              | memOp x => exact evaluate_ordinaryOp_clock env state trace _ args (by simp) (by simp)
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl

/-- The termination-only clock clamp does not change the result of the
proof-side evaluator. HOL correspondence for the evaluator remains open. -/
theorem fixClock_evaluate {C F : Type} (expressions : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    fixClock state (evaluate expressions env state) = evaluate expressions env state := by
  have bound := evaluate_clock_le expressions env state
  cases run : evaluate expressions env state with
  | mk result next =>
    simp only [run] at bound
    simp [fixClock, Nat.min_eq_right bound]

end Flapjack.Compiler.Backend.ClosSem
