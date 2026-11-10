module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateOracleAdvance
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode

@[expose] public section

/-! Code/oracle history for the proof-side closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A finite history of installations. Each step installs the current
oracle entry's auxiliary code and advances the oracle once. This is
Flapjack-specific infrastructure for tracking exact code evolution, not a
port of a HOL declaration. -/
inductive OracleCodeHistory {C : Type} :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) → CompileOracle C →
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) → CompileOracle C → Prop where
  | refl (code oracle) : OracleCodeHistory code oracle code oracle
  | install (code oracle) :
      OracleCodeHistory code oracle (code.updateListEq (oracle 0).2.2) (holShiftSeq 1 oracle)
  | trans {firstCode middleCode lastCode firstOracle middleOracle lastOracle} :
      OracleCodeHistory firstCode firstOracle middleCode middleOracle →
      OracleCodeHistory middleCode middleOracle lastCode lastOracle →
      OracleCodeHistory firstCode firstOracle lastCode lastOracle

/-- A history can be used between states whose code and oracle fields agree.
This is Flapjack-specific infrastructure. -/
theorem oracleCodeHistory_of_fields {C F : Type} (source next : State C F)
    (code : next.code = source.code) (oracle : next.compileOracle = source.compileOracle) :
    OracleCodeHistory source.code source.compileOracle next.code next.compileOracle := by
  rw [code, oracle]
  exact .refl _ _

/-- Every installation produces an exact code/oracle history, including
invalid inputs and the valid-install timeout path. This is Flapjack-specific
infrastructure, not a port of a HOL theorem. -/
theorem doInstall_oracleCodeHistory {C F : Type} (values : List Value) (source next : State C F)
    (result : Result (List ClosLang.Exp) Value) (run : doInstall values source = (result, next)) :
    OracleCodeHistory source.code source.compileOracle next.code next.compileOracle := by
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have nextEq : next = source := by
      unfold doInstall at run
      repeat' first | split at run | simp_all
    subst next
    exact .refl _ _
  · obtain ⟨_, _, _, _, _, _, auxiliary, _, _, _, _, oracleRun, _, _, _, _, _, nextEq, _⟩ :=
      doInstall_nonType_parts values source next result run typeError
    have auxEq : auxiliary = (source.compileOracle 0).2.2 := by simp [oracleRun]
    rw [nextEq]
    simpa [auxEq] using OracleCodeHistory.install source.code source.compileOracle

/-- Successful primitive operations do not add history steps. This is
Flapjack-specific infrastructure. -/
theorem doApp_oracleCodeHistory {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source next : State C F) (value : Value) (run : doApp op args source = .val (value, next)) :
    OracleCodeHistory source.code source.compileOracle next.code next.compileOracle := by
  obtain ⟨code, oracle⟩ := doApp_codeOracle op args source next value run
  exact oracleCodeHistory_of_fields source next code oracle

/-- Exact code/oracle history for all results of an expression evaluation.
This is Flapjack-specific simulation infrastructure. -/
def EvaluateOracleCodeHistoryAt {C F : Type} (source : State C F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) →
      OracleCodeHistory source.code source.compileOracle next.code next.compileOracle

/-- Empty expression lists leave code and oracle unchanged. -/
theorem evaluate_nil_oracleCodeHistory {C F : Type} (source : State C F) : EvaluateOracleCodeHistoryAt source [] := by
  intro env result next run
  simp [evaluate] at run
  obtain ⟨_, rfl⟩ := run
  exact .refl _ _

/-- Variable evaluation leaves code and oracle unchanged. -/
theorem evaluate_var_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (source : State C F) : EvaluateOracleCodeHistoryAt source [.var trace index] := by
  intro env result next run
  simp only [evaluate] at run
  split at run <;> simp_all [OracleCodeHistory.refl]

/-- Closure creation leaves code and oracle unchanged. -/
theorem evaluate_fn_oracleCodeHistory {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (source : State C F) : EvaluateOracleCodeHistoryAt source [.fn name location selected arity body] := by
  intro env result next run
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run <;> simp_all [OracleCodeHistory.refl]

/-- Sequencing composes the two exact code/oracle histories. -/
theorem evaluate_cons_oracleCodeHistory {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (source : State C F) (firstIH : EvaluateOracleCodeHistoryAt source [first])
    (restIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateOracleCodeHistoryAt state (second :: rest)) :
    EvaluateOracleCodeHistoryAt source (first :: second :: rest) := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    have firstGrowth := firstIH env firstResult middle firstRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [first] env source
      simpa [firstRun] using h
    rw [firstRun] at run
    cases firstResult with
    | err error => cases run; exact firstGrowth
    | val values =>
      dsimp only at run
      cases restRun : evaluate (second :: rest) env middle with
      | mk restResult last =>
        have restGrowth := restIH middle middleClock env restResult last restRun
        rw [restRun] at run
        cases restResult <;> cases run <;> exact .trans firstGrowth restGrowth

theorem evaluate_raise_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvaluateOracleCodeHistoryAt source [body]) :
    EvaluateOracleCodeHistoryAt source [.raise trace body] := by
  intro env result next run
  rw [evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have growth := bodyIH env bodyResult middle bodyRun
    rw [bodyRun] at run
    cases bodyResult <;> cases run <;> exact growth

/-- A tick changes only the clock before evaluating its body. -/
theorem evaluate_tick_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvaluateOracleCodeHistoryAt (decClock 1 source) [body]) :
    EvaluateOracleCodeHistoryAt source [.tick trace body] := by
  intro env result next run
  by_cases zero : source.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨_, rfl⟩ := run
    exact OracleCodeHistory.refl _ _
  · have bodyRun : evaluate [body] env (decClock 1 source) = (result, next) := by
      simpa [evaluate, zero] using run
    simpa [decClock] using bodyIH env result next bodyRun

/-- Let bindings compose oracle shifts from bindings and body. -/
theorem evaluate_let_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (source : State C F)
    (bindingsIH : EvaluateOracleCodeHistoryAt source bindings)
    (bodyIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateOracleCodeHistoryAt state [body]) :
    EvaluateOracleCodeHistoryAt source [.let trace bindings body] := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate bindings env source with
  | mk bindingsResult middle =>
    have growth := bindingsIH env bindingsResult middle bindingsRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le bindings env source
      simpa [bindingsRun] using h
    rw [bindingsRun] at run
    cases bindingsResult with
    | err error => cases run; exact growth
    | val values => exact OracleCodeHistory.trans growth (bodyIH middle middleClock (values ++ env) result next run)

/-- Handlers compose oracle shifts from the body and a raised-value handler. -/
theorem evaluate_handle_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (source : State C F) (bodyIH : EvaluateOracleCodeHistoryAt source [body])
    (handlerIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateOracleCodeHistoryAt state [handler]) :
    EvaluateOracleCodeHistoryAt source [.handle trace body handler] := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have growth := bodyIH env bodyResult middle bodyRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [body] env source
      simpa [bodyRun] using h
    rw [bodyRun] at run
    cases bodyResult with
    | val values => cases run; exact growth
    | err error =>
      cases error with
      | abort reason => cases run; exact growth
      | raise value => exact OracleCodeHistory.trans growth (handlerIH middle middleClock (value :: env) result next run)

/-- Conditionals compose oracle shifts through the condition and selected branch. -/
theorem evaluate_if_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (source : State C F) (conditionIH : EvaluateOracleCodeHistoryAt source [condition])
    (yesIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateOracleCodeHistoryAt state [yes])
    (noIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateOracleCodeHistoryAt state [no]) :
    EvaluateOracleCodeHistoryAt source [.ifThenElse trace condition yes no] := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases testRun : evaluate [condition] env source with
  | mk testResult middle =>
    have growth := conditionIH env testResult middle testRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [condition] env source
      simpa [testRun] using h
    rw [testRun] at run
    cases testResult with
    | err error => cases run; exact growth
    | val values =>
      dsimp only at run
      split at run
      · cases run; exact growth
      · exact OracleCodeHistory.trans growth (yesIH middle middleClock env result next run)
      · exact OracleCodeHistory.trans growth (noIH middle middleClock env result next run)

/-- Recursive closure creation leaves the oracle unchanged before the body. -/
theorem evaluate_letrec_oracleCodeHistory {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (source : State C F) (bodyIH : EvaluateOracleCodeHistoryAt source [body]) :
    EvaluateOracleCodeHistoryAt source [.letrec names location selected functions body] := by
  intro env result next run
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run
  all_goals try (simp_all [OracleCodeHistory.refl]; done)
  all_goals exact bodyIH _ result next run

/-- Ordinary operations preserve the oracle after evaluating their arguments. -/
theorem evaluate_ordinaryOp_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) (source : State C F)
    (argsIH : EvaluateOracleCodeHistoryAt source args) : EvaluateOracleCodeHistoryAt source [.op trace op args] := by
  intro env result next run
  rw [evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have growth := argsIH env argsResult middle argsRun
    rw [argsRun] at run
    cases argsResult with
    | err error => cases run; exact growth
    | val values =>
      dsimp only at run
      cases appRun : doApp op values.reverse middle with
      | err error =>
        rw [appRun] at run
        cases run
        exact growth
      | val pair =>
        obtain ⟨value, final⟩ := pair
        rw [appRun] at run
        cases run
        obtain ⟨sameCode, sameOracle⟩ := doApp_codeOracle op values.reverse middle next value appRun
        simpa [sameCode, sameOracle] using growth

/-- Installation composes argument, installation, and installed-program
oracle shifts, including the valid-install timeout case. -/
theorem evaluate_install_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvaluateOracleCodeHistoryAt source args)
    (programIH : ∀ program (state : State C F), state.clock < source.clock → EvaluateOracleCodeHistoryAt state program) :
    EvaluateOracleCodeHistoryAt source [.op trace .install args] := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have growth := argsIH env argsResult middle argsRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error => cases run; exact growth
    | val values =>
      dsimp only at run
      cases installRun : doInstall values.reverse middle with
      | mk installResult installed =>
        have installedGrowth : OracleCodeHistory middle.code middle.compileOracle installed.code installed.compileOracle :=
          doInstall_oracleCodeHistory values.reverse middle installed installResult installRun
        rw [installRun] at run
        cases installResult with
        | err error => cases run; exact OracleCodeHistory.trans growth installedGrowth
        | val program =>
          dsimp only at run
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            have installedClock := doInstall_success_clock values.reverse middle installed program installRun
            have smaller : installed.clock < source.clock := by omega
            have finalGrowth := programIH program installed smaller [] programResult final programRun
            rw [programRun] at run
            cases programResult <;> cases run <;>
              exact OracleCodeHistory.trans growth (OracleCodeHistory.trans installedGrowth finalGrowth)

/-- A forced thunk composes the oracle shifts of its arguments and generated call. -/
theorem evaluate_force_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (source : State C F) (argsIH : EvaluateOracleCodeHistoryAt source args)
    (forceIH : ∀ state : State C F, state.clock ≤ source.clock →
      EvaluateOracleCodeHistoryAt state [appUnit (.var .none 0)]) :
    EvaluateOracleCodeHistoryAt source [.op trace (.thunkOp .forceThunk) args] := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have growth := argsIH env argsResult middle argsRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error => cases run; exact growth
    | val values =>
      dsimp only at run
      cases dest : destThunk values middle.refs with
      | badRef | notThunk => simp [dest] at run; obtain ⟨_, rfl⟩ := run; exact growth
      | isThunk mode value =>
        cases mode with
        | evaluated => simp [dest] at run; obtain ⟨_, rfl⟩ := run; exact growth
        | notEvaluated =>
          simp only [dest] at run
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
          | mk forceResult last =>
            have lastGrowth := forceIH middle middleClock [value] forceResult last forceRun
            rw [forceRun] at run
            cases forceResult with
            | err error => cases run; exact OracleCodeHistory.trans growth lastGrowth
            | val forced =>
              dsimp only at run
              cases update : updateThunk values last.refs forced with
              | none => simp [update] at run; obtain ⟨_, rfl⟩ := run; exact OracleCodeHistory.trans growth lastGrowth
              | some refs =>
                simp [update] at run
                obtain ⟨_, rfl⟩ := run
                exact OracleCodeHistory.trans growth lastGrowth

/-- Application oracle-shift hypotheses at clocks below a bound. -/
def AppOracleCodeHistoryBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (location : Option Nat) (function : Value) (args : List Value)
    (source next : State C F) (result : Result (List Value) Value),
    source.clock < clock → evaluateApp location function args source = (result, next) →
    OracleCodeHistory source.code source.compileOracle next.code next.compileOracle

/-- One closure application composes body and remaining-argument shifts at
smaller clocks. -/
theorem evaluateApp_oracleCodeHistory {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (source next : State C F) (result : Result (List Value) Value)
    (run : evaluateApp location function args source = (result, next))
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (start final : State C F)
      (result : Result (List Value) Value), start.clock < source.clock →
      evaluate [body] env start = (result, final) → OracleCodeHistory start.code start.compileOracle final.code final.compileOracle)
    (appIH : AppOracleCodeHistoryBelow (C := C) (F := F) source.clock) : OracleCodeHistory source.code source.compileOracle next.code next.compileOracle := by
  cases args with
  | nil => simp [evaluateApp] at run; obtain ⟨_, rfl⟩ := run; exact OracleCodeHistory.refl _ _
  | cons first rest =>
    rw [evaluateApp] at run
    cases found : destClosure source.maxApp location function (first :: rest) with
    | none => rw [found] at run; cases run; exact OracleCodeHistory.refl _ _
    | some kind =>
      rw [found] at run
      cases kind with
      | partialApp value =>
        dsimp only at run
        split at run <;> simp [decClock] at run <;>
          obtain ⟨_, rfl⟩ := run <;> exact OracleCodeHistory.refl _ _
      | fullApp body env remaining =>
        dsimp only at run
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ found)
        split at run
        · simp at run
          obtain ⟨_, rfl⟩ := run
          exact OracleCodeHistory.refl _ _
        · have smaller : (decClock cost source).clock < source.clock := by simp [decClock]; omega
          rw [fixClock_evaluate] at run
          cases bodyRun : evaluate [body] env (decClock cost source) with
          | mk bodyResult middle =>
            have bodyGrowth : OracleCodeHistory source.code source.compileOracle middle.code middle.compileOracle := by
              simpa [decClock] using bodyIH body env (decClock cost source) middle bodyResult smaller bodyRun
            have clockLe : middle.clock ≤ (decClock cost source).clock := by
              have h := evaluate_clock_le [body] env (decClock cost source)
              simpa [bodyRun] using h
            rw [bodyRun] at run
            cases bodyResult with
            | err error => cases run; exact bodyGrowth
            | val values =>
              cases values with
              | nil => cases run; exact bodyGrowth
              | cons value tail =>
                cases tail with
                | nil =>
                  exact OracleCodeHistory.trans bodyGrowth (appIH location value remaining middle next result (by omega) run)
                | cons other tail => cases run; exact bodyGrowth

/-- Application expressions compose oracle shifts through argument, function and
closure-application evaluation. -/
theorem evaluate_app_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (source : State C F)
    (argsIH : EvaluateOracleCodeHistoryAt source args)
    (functionIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateOracleCodeHistoryAt state [function])
    (appIH : AppOracleCodeHistoryBelow (C := C) (F := F) (source.clock + 1)) :
    EvaluateOracleCodeHistoryAt source [.app trace location function args] := by
  intro env result next run
  cases args with
  | nil => simp [evaluate] at run; obtain ⟨_, rfl⟩ := run; exact OracleCodeHistory.refl _ _
  | cons first rest =>
    rw [evaluate, fixClock_evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      have growth := argsIH env argsResult middle argsRun
      have middleClock : middle.clock ≤ source.clock := by
        have h := evaluate_clock_le (first :: rest) env source
        simpa [argsRun] using h
      rw [argsRun] at run
      cases argsResult with
      | err error => cases run; exact growth
      | val values =>
        rw [fixClock_evaluate] at run
        cases functionRun : evaluate [function] env middle with
        | mk functionResult last =>
          have lastGrowth := functionIH middle middleClock env functionResult last functionRun
          rw [functionRun] at run
          cases functionResult with
          | err error => cases run; exact OracleCodeHistory.trans growth lastGrowth
          | val functions =>
            have lastClock : last.clock ≤ source.clock := by
              have h := evaluate_clock_le [function] env middle
              simp only [functionRun] at h
              omega
            exact OracleCodeHistory.trans growth (OracleCodeHistory.trans lastGrowth
              (appIH location _ values last next result (by omega) run))

/-- A direct call composes oracle shifts through its arguments and selected body. -/
theorem evaluate_call_oracleCodeHistory {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvaluateOracleCodeHistoryAt source args)
    (bodyIH : ∀ body (state : State C F), state.clock < source.clock → EvaluateOracleCodeHistoryAt state [body]) :
    EvaluateOracleCodeHistoryAt source [.call trace ticks location args] := by
  intro env result next run
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have growth := argsIH env argsResult middle argsRun
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error => cases run; exact growth
    | val values =>
      dsimp only at run
      cases found : findCode location values middle.code with
      | none => rw [found] at run; cases run; exact growth
      | some entry =>
        obtain ⟨bodyEnv, body⟩ := entry
        rw [found] at run
        dsimp only at run
        split at run
        · simp at run; obtain ⟨_, rfl⟩ := run; exact growth
        · have smaller : (decClock (ticks + 1) middle).clock < source.clock := by simp [decClock]; omega
          have bodyGrowth := bodyIH body (decClock (ticks + 1) middle) smaller bodyEnv result next run
          exact OracleCodeHistory.trans growth (by simpa [decClock] using bodyGrowth)

/-- Evaluation and application advance their input oracle by a finite amount,
even on errors. This mutual result is Flapjack induction infrastructure. -/
theorem evaluate_oracleCodeHistory {C F : Type} :
    (∀ expressions env (source next : State C F) result,
      evaluate expressions env source = (result, next) → OracleCodeHistory source.code source.compileOracle next.code next.compileOracle) ∧
    (∀ clock, AppOracleCodeHistoryBelow (C := C) (F := F) clock) := by
  have all : ∀ clock : Nat,
      (∀ source : State C F, source.clock = clock → ∀ location function args next result,
        evaluateApp location function args source = (result, next) → OracleCodeHistory source.code source.compileOracle next.code next.compileOracle) ∧
      (∀ weight expressions (source : State C F),
        source.clock = clock → expsWeight expressions = weight → EvaluateOracleCodeHistoryAt source expressions) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ source : State C F, source.clock = clock → ∀ location function args next result,
          evaluateApp location function args source = (result, next) → OracleCodeHistory source.code source.compileOracle next.code next.compileOracle := by
        intro source clockEq location function args next result run
        apply evaluateApp_oracleCodeHistory location function args source next result run
        · intro body env start final result smaller bodyRun
          exact (clockIH start.clock (by omega)).2 (expsWeight [body]) [body] start rfl rfl env result final bodyRun
        · intro location function args state final result smaller appRun
          exact (clockIH state.clock (by omega)).1 state rfl location function args final result appRun
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions (state : State C F), state.clock ≤ clock →
              expsWeight expressions < weight → EvaluateOracleCodeHistoryAt state expressions := by
            intro expressions state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions state clockEq rfl
          have appBound : AppOracleCodeHistoryBelow (C := C) (F := F) (clock + 1) := by
            intro location function args state final result smaller run
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ smaller) with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 state rfl location function args final result run
            · exact appAll state clockEq location function args final result run
          intro expressions source clockEq measure
          cases expressions with
          | nil => exact evaluate_nil_oracleCodeHistory source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_oracleCodeHistory first second tail source
              · apply exprIH [first] source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro state bound
                apply exprIH (second :: tail) state (by omega)
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact evaluate_var_oracleCodeHistory trace index source
              | fn name location selected arity body => exact evaluate_fn_oracleCodeHistory name location selected arity body source
              | raise trace body =>
                apply evaluate_raise_oracleCodeHistory trace body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_oracleCodeHistory trace body source
                apply exprIH [body] (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluate_call_oracleCodeHistory trace ticks location args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
              | «let» trace bindings body =>
                apply evaluate_let_oracleCodeHistory trace bindings body source
                · apply exprIH bindings source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [body] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_oracleCodeHistory names location selected functions body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_oracleCodeHistory trace body handler source
                · apply exprIH [body] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [handler] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_oracleCodeHistory trace condition yes no source
                · apply exprIH [condition] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [yes] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [no] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_oracleCodeHistory trace location function args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [function] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · simpa [clockEq] using appBound
              | op trace op args =>
                have argsSmaller : expsWeight args < weight := by
                  have h := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                have argsIH := exprIH args source (by omega) argsSmaller
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    EvaluateOracleCodeHistoryAt source [.op trace op args] := by
                  intro op notInstall notForce
                  exact evaluate_ordinaryOp_oracleCodeHistory trace op args notInstall notForce source argsIH
                cases op with
                | install =>
                  apply evaluate_install_oracleCodeHistory trace args source argsIH
                  intro program state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight program) program state rfl rfl
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_oracleCodeHistory trace args source argsIH
                    intro state bound
                    apply exprIH [appUnit (.var .none 0)] state (by omega)
                    have h := appUnit_var_weight
                    simp only [expsWeight, expWeight] at measure
                    simp only [appUnit, expsWeight, expWeight] at h ⊢
                    omega
                  | allocThunk mode => exact ordinary _ (by simp) (by simp)
                  | updateThunk mode => exact ordinary _ (by simp) (by simp)
                | label index => exact ordinary _ (by simp) (by simp)
                | ffi name => exact ordinary _ (by simp) (by simp)
                | intOp operation => exact ordinary _ (by simp) (by simp)
                | wordOp operation => exact ordinary _ (by simp) (by simp)
                | blockOp operation => exact ordinary _ (by simp) (by simp)
                | globOp operation => exact ordinary _ (by simp) (by simp)
                | memOp operation => exact ordinary _ (by simp) (by simp)
  constructor
  · intro expressions env source next result run
    exact (all source.clock).2 (expsWeight expressions) expressions source rfl rfl env result next run
  · intro clock location function args source next result smaller run
    exact (all source.clock).1 source rfl location function args next result run


/-- Apply the auxiliary code of a finite oracle prefix in installation order.
This is Flapjack-specific history infrastructure. -/
def installOraclePrefix {C : Type} (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : CompileOracle C) : Nat → HolFiniteMapExact Nat (Nat × ClosLang.Exp)
  | 0 => code
  | n + 1 => installOraclePrefix (code.updateListEq (oracle 0).2.2) (holShiftSeq 1 oracle) n

/-- Installing two consecutive oracle prefixes equals installing their
concatenation. This is Flapjack-specific history infrastructure. -/
theorem installOraclePrefix_add {C : Type} (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : CompileOracle C) (n m : Nat) :
    installOraclePrefix code oracle (n + m) =
      installOraclePrefix (installOraclePrefix code oracle n) (holShiftSeq n oracle) m := by
  induction n generalizing code oracle with
  | zero =>
    have shiftZero : holShiftSeq 0 oracle = oracle := by
      funext index
      simp [holShiftSeq]
    simp [installOraclePrefix, shiftZero]
  | succ n ih =>
    simp only [Nat.succ_add, installOraclePrefix]
    rw [ih]
    congr 1

/-- Every code/oracle history is exactly a finite oracle shift together with
installation of the same prefix's auxiliary code. This is Flapjack-specific
history infrastructure. -/
theorem OracleCodeHistory.prefix {C : Type}
    {firstCode lastCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    {firstOracle lastOracle : CompileOracle C}
    (history : OracleCodeHistory firstCode firstOracle lastCode lastOracle) :
    ∃ count, lastOracle = holShiftSeq count firstOracle ∧ lastCode = installOraclePrefix firstCode firstOracle count := by
  induction history with
  | refl code oracle =>
    refine ⟨0, ?_, rfl⟩
    funext index
    simp [holShiftSeq]
  | install code oracle =>
    exact ⟨1, rfl, rfl⟩
  | @trans firstCode middleCode lastCode firstOracle middleOracle lastOracle _ _ firstIH secondIH =>
    obtain ⟨n, middleOracleEq, middleCodeEq⟩ := firstIH
    obtain ⟨m, lastOracleEq, lastCodeEq⟩ := secondIH
    refine ⟨n + m, ?_, ?_⟩
    · rw [lastOracleEq, middleOracleEq]
      funext index
      simp [holShiftSeq, Nat.add_comm, Nat.add_left_comm]
    · rw [lastCodeEq, middleCodeEq, middleOracleEq, installOraclePrefix_add]

/-- Evaluation and application expose matching finite prefixes for both the
oracle and the exact code map. This is Flapjack-specific history infrastructure. -/
theorem evaluate_oracleCodePrefix {C F : Type} (expressions : List ClosLang.Exp) (env : List Value)
    (source next : State C F) (result : Result (List Value) Value)
    (run : evaluate expressions env source = (result, next)) :
    ∃ count, next.compileOracle = holShiftSeq count source.compileOracle ∧
      next.code = installOraclePrefix source.code source.compileOracle count := by
  exact (evaluate_oracleCodeHistory.1 expressions env source next result run).prefix

/-- Closure application exposes matching finite prefixes for the oracle and
exact code map. This is Flapjack-specific history infrastructure. -/
theorem evaluateApp_oracleCodePrefix {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (source next : State C F) (result : Result (List Value) Value)
    (run : evaluateApp location function args source = (result, next)) :
    ∃ count, next.compileOracle = holShiftSeq count source.compileOracle ∧
      next.code = installOraclePrefix source.code source.compileOracle count := by
  exact ((evaluate_oracleCodeHistory (C := C) (F := F)).2 (source.clock + 1)
    location function args source next result (by omega) run).prefix

end Flapjack.Compiler.Backend.ClosSem
