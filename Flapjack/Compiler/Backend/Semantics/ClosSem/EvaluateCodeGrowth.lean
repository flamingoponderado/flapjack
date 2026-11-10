module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.InstallGrowth
public import Flapjack.FiniteMap.SubmapExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

@[expose] public section

/-! Code-store growth in the proof-side closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- The expression evaluator preserves the original code entries. -/
def EvaluateCodeGrowthAt {C F : Type} (source : State C F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) → source.code.submap next.code

/-- Empty expression lists preserve their code map. -/
theorem evaluate_nil_codeGrowth {C F : Type} (source : State C F) : EvaluateCodeGrowthAt source [] := by
  intro env result next run
  simp [evaluate] at run
  obtain ⟨_, rfl⟩ := run
  exact HolFiniteMapExact.submap_refl _

/-- Variable evaluation preserves the code map. -/
theorem evaluate_var_codeGrowth {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (source : State C F) : EvaluateCodeGrowthAt source [.var trace index] := by
  intro env result next run
  simp only [evaluate] at run
  split at run <;> simp_all [HolFiniteMapExact.submap_refl]

/-- Closure creation preserves the code map. -/
theorem evaluate_fn_codeGrowth {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (source : State C F) : EvaluateCodeGrowthAt source [.fn name location selected arity body] := by
  intro env result next run
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run <;> simp_all [HolFiniteMapExact.submap_refl]

/-- Sequencing composes the code-growth relations of its two evaluations. -/
theorem evaluate_cons_codeGrowth {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (source : State C F) (firstIH : EvaluateCodeGrowthAt source [first])
    (restIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateCodeGrowthAt state (second :: rest)) :
    EvaluateCodeGrowthAt source (first :: second :: rest) := by
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
        cases restResult <;> cases run <;> exact HolFiniteMapExact.submap_trans firstGrowth restGrowth

/-- Raising a value retains the operand's code growth. -/
theorem evaluate_raise_codeGrowth {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvaluateCodeGrowthAt source [body]) :
    EvaluateCodeGrowthAt source [.raise trace body] := by
  intro env result next run
  rw [evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have growth := bodyIH env bodyResult middle bodyRun
    rw [bodyRun] at run
    cases bodyResult <;> cases run <;> exact growth

/-- A tick changes only the clock before evaluating its body. -/
theorem evaluate_tick_codeGrowth {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvaluateCodeGrowthAt (decClock 1 source) [body]) :
    EvaluateCodeGrowthAt source [.tick trace body] := by
  intro env result next run
  by_cases zero : source.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨_, rfl⟩ := run
    exact HolFiniteMapExact.submap_refl _
  · have bodyRun : evaluate [body] env (decClock 1 source) = (result, next) := by
      simpa [evaluate, zero] using run
    simpa [decClock] using bodyIH env result next bodyRun

/-- Let bindings compose code growth from bindings and body. -/
theorem evaluate_let_codeGrowth {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (source : State C F)
    (bindingsIH : EvaluateCodeGrowthAt source bindings)
    (bodyIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateCodeGrowthAt state [body]) :
    EvaluateCodeGrowthAt source [.let trace bindings body] := by
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
    | val values => exact HolFiniteMapExact.submap_trans growth (bodyIH middle middleClock (values ++ env) result next run)

/-- Handlers preserve code across both the body and a raised-value handler. -/
theorem evaluate_handle_codeGrowth {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (source : State C F) (bodyIH : EvaluateCodeGrowthAt source [body])
    (handlerIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateCodeGrowthAt state [handler]) :
    EvaluateCodeGrowthAt source [.handle trace body handler] := by
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
      | raise value => exact HolFiniteMapExact.submap_trans growth (handlerIH middle middleClock (value :: env) result next run)

/-- Conditionals preserve code through the condition and the selected branch. -/
theorem evaluate_if_codeGrowth {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (source : State C F) (conditionIH : EvaluateCodeGrowthAt source [condition])
    (yesIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateCodeGrowthAt state [yes])
    (noIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateCodeGrowthAt state [no]) :
    EvaluateCodeGrowthAt source [.ifThenElse trace condition yes no] := by
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
      · exact HolFiniteMapExact.submap_trans growth (yesIH middle middleClock env result next run)
      · exact HolFiniteMapExact.submap_trans growth (noIH middle middleClock env result next run)

/-- Recursive closure creation leaves code alone before evaluating its body. -/
theorem evaluate_letrec_codeGrowth {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (source : State C F) (bodyIH : EvaluateCodeGrowthAt source [body]) :
    EvaluateCodeGrowthAt source [.letrec names location selected functions body] := by
  intro env result next run
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run
  all_goals try (simp_all [HolFiniteMapExact.submap_refl]; done)
  all_goals exact bodyIH _ result next run

/-- Ordinary operations preserve code after their arguments have evaluated. -/
theorem evaluate_ordinaryOp_codeGrowth {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) (source : State C F)
    (argsIH : EvaluateCodeGrowthAt source args) : EvaluateCodeGrowthAt source [.op trace op args] := by
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
        have same := (doApp_codeOracle op values.reverse middle next value appRun).1
        simpa [same] using growth

/-- Installation composes argument, installation, and installed-program
code growth, including the valid-install timeout case. -/
theorem evaluate_install_codeGrowth {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvaluateCodeGrowthAt source args)
    (programIH : ∀ program (state : State C F), state.clock < source.clock → EvaluateCodeGrowthAt state program) :
    EvaluateCodeGrowthAt source [.op trace .install args] := by
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
        have installedGrowth : middle.code.submap installed.code :=
          doInstall_code_submap values.reverse middle installed installResult installRun
        rw [installRun] at run
        cases installResult with
        | err error => cases run; exact HolFiniteMapExact.submap_trans growth installedGrowth
        | val program =>
          dsimp only at run
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            have installedClock := doInstall_success_clock values.reverse middle installed program installRun
            have smaller : installed.clock < source.clock := by omega
            have finalGrowth := programIH program installed smaller [] programResult final programRun
            rw [programRun] at run
            cases programResult <;> cases run <;>
              exact HolFiniteMapExact.submap_trans growth (HolFiniteMapExact.submap_trans installedGrowth finalGrowth)

/-- A forced thunk preserves argument code growth and any code installed by
its generated call. -/
theorem evaluate_force_codeGrowth {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (source : State C F) (argsIH : EvaluateCodeGrowthAt source args)
    (forceIH : ∀ state : State C F, state.clock ≤ source.clock →
      EvaluateCodeGrowthAt state [appUnit (.var .none 0)]) :
    EvaluateCodeGrowthAt source [.op trace (.thunkOp .forceThunk) args] := by
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
            | err error => cases run; exact HolFiniteMapExact.submap_trans growth lastGrowth
            | val forced =>
              dsimp only at run
              cases update : updateThunk values last.refs forced with
              | none => simp [update] at run; obtain ⟨_, rfl⟩ := run; exact HolFiniteMapExact.submap_trans growth lastGrowth
              | some refs =>
                simp [update] at run
                obtain ⟨_, rfl⟩ := run
                exact HolFiniteMapExact.submap_trans growth lastGrowth

/-- Application code-growth hypotheses at clocks below a bound. -/
def AppCodeGrowthBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (location : Option Nat) (function : Value) (args : List Value)
    (source next : State C F) (result : Result (List Value) Value),
    source.clock < clock → evaluateApp location function args source = (result, next) →
    source.code.submap next.code

/-- One closure application composes body and remaining-argument growth at
smaller clocks. -/
theorem evaluateApp_codeGrowth {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (source next : State C F) (result : Result (List Value) Value)
    (run : evaluateApp location function args source = (result, next))
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (start final : State C F)
      (result : Result (List Value) Value), start.clock < source.clock →
      evaluate [body] env start = (result, final) → start.code.submap final.code)
    (appIH : AppCodeGrowthBelow (C := C) (F := F) source.clock) : source.code.submap next.code := by
  cases args with
  | nil => simp [evaluateApp] at run; obtain ⟨_, rfl⟩ := run; exact HolFiniteMapExact.submap_refl _
  | cons first rest =>
    rw [evaluateApp] at run
    cases found : destClosure source.maxApp location function (first :: rest) with
    | none => rw [found] at run; cases run; exact HolFiniteMapExact.submap_refl _
    | some kind =>
      rw [found] at run
      cases kind with
      | partialApp value =>
        dsimp only at run
        split at run <;> simp [decClock] at run <;>
          obtain ⟨_, rfl⟩ := run <;> exact HolFiniteMapExact.submap_refl _
      | fullApp body env remaining =>
        dsimp only at run
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ found)
        split at run
        · simp at run
          obtain ⟨_, rfl⟩ := run
          exact HolFiniteMapExact.submap_refl _
        · have smaller : (decClock cost source).clock < source.clock := by simp [decClock]; omega
          rw [fixClock_evaluate] at run
          cases bodyRun : evaluate [body] env (decClock cost source) with
          | mk bodyResult middle =>
            have bodyGrowth : source.code.submap middle.code := by
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
                  exact HolFiniteMapExact.submap_trans bodyGrowth (appIH location value remaining middle next result (by omega) run)
                | cons other tail => cases run; exact bodyGrowth

/-- Application expressions retain code through argument, function and
closure-application evaluation. -/
theorem evaluate_app_codeGrowth {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (source : State C F)
    (argsIH : EvaluateCodeGrowthAt source args)
    (functionIH : ∀ state : State C F, state.clock ≤ source.clock → EvaluateCodeGrowthAt state [function])
    (appIH : AppCodeGrowthBelow (C := C) (F := F) (source.clock + 1)) :
    EvaluateCodeGrowthAt source [.app trace location function args] := by
  intro env result next run
  cases args with
  | nil => simp [evaluate] at run; obtain ⟨_, rfl⟩ := run; exact HolFiniteMapExact.submap_refl _
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
          | err error => cases run; exact HolFiniteMapExact.submap_trans growth lastGrowth
          | val functions =>
            have lastClock : last.clock ≤ source.clock := by
              have h := evaluate_clock_le [function] env middle
              simp only [functionRun] at h
              omega
            exact HolFiniteMapExact.submap_trans growth (HolFiniteMapExact.submap_trans lastGrowth
              (appIH location _ values last next result (by omega) run))

/-- A direct call retains code through its arguments and its selected body. -/
theorem evaluate_call_codeGrowth {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvaluateCodeGrowthAt source args)
    (bodyIH : ∀ body (state : State C F), state.clock < source.clock → EvaluateCodeGrowthAt state [body]) :
    EvaluateCodeGrowthAt source [.call trace ticks location args] := by
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
          exact HolFiniteMapExact.submap_trans growth (by simpa [decClock] using bodyGrowth)

/-- Evaluation and application retain all code entries, even on errors.
This proof-side result remains untagged pending HOL carrier review. -/
theorem evaluate_code_growth {C F : Type} :
    (∀ expressions env (source next : State C F) result,
      evaluate expressions env source = (result, next) → source.code.submap next.code) ∧
    (∀ clock, AppCodeGrowthBelow (C := C) (F := F) clock) := by
  have all : ∀ clock : Nat,
      (∀ source : State C F, source.clock = clock → ∀ location function args next result,
        evaluateApp location function args source = (result, next) → source.code.submap next.code) ∧
      (∀ weight expressions (source : State C F),
        source.clock = clock → expsWeight expressions = weight → EvaluateCodeGrowthAt source expressions) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ source : State C F, source.clock = clock → ∀ location function args next result,
          evaluateApp location function args source = (result, next) → source.code.submap next.code := by
        intro source clockEq location function args next result run
        apply evaluateApp_codeGrowth location function args source next result run
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
              expsWeight expressions < weight → EvaluateCodeGrowthAt state expressions := by
            intro expressions state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions state clockEq rfl
          have appBound : AppCodeGrowthBelow (C := C) (F := F) (clock + 1) := by
            intro location function args state final result smaller run
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ smaller) with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 state rfl location function args final result run
            · exact appAll state clockEq location function args final result run
          intro expressions source clockEq measure
          cases expressions with
          | nil => exact evaluate_nil_codeGrowth source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_codeGrowth first second tail source
              · apply exprIH [first] source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro state bound
                apply exprIH (second :: tail) state (by omega)
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact evaluate_var_codeGrowth trace index source
              | fn name location selected arity body => exact evaluate_fn_codeGrowth name location selected arity body source
              | raise trace body =>
                apply evaluate_raise_codeGrowth trace body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_codeGrowth trace body source
                apply exprIH [body] (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluate_call_codeGrowth trace ticks location args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
              | «let» trace bindings body =>
                apply evaluate_let_codeGrowth trace bindings body source
                · apply exprIH bindings source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [body] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_codeGrowth names location selected functions body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_codeGrowth trace body handler source
                · apply exprIH [body] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [handler] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_codeGrowth trace condition yes no source
                · apply exprIH [condition] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [yes] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [no] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_codeGrowth trace location function args source
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
                    EvaluateCodeGrowthAt source [.op trace op args] := by
                  intro op notInstall notForce
                  exact evaluate_ordinaryOp_codeGrowth trace op args notInstall notForce source argsIH
                cases op with
                | install =>
                  apply evaluate_install_codeGrowth trace args source argsIH
                  intro program state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight program) program state rfl rfl
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_codeGrowth trace args source argsIH
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

end Flapjack.Compiler.Backend.ClosSem
