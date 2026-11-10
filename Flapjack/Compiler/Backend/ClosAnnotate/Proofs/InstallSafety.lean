module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EvaluateCases
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode

@[expose] public section

/-! Code and oracle safety across closure-language installation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Ordinary primitive execution preserves the code and oracle invariants. -/
theorem doApp_preserves_safe {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source next : State C F) (value : Value) (run : doApp op args source = .val (value, next))
    (code : CodeSafe source) (oracle : OracleSafe source) : CodeSafe next ∧ OracleSafe next := by
  obtain ⟨codeEq, oracleEq⟩ := doApp_codeOracle op args source next value run
  constructor
  · intro key arity body found
    rw [codeEq] at found
    exact code key arity body found
  · simpa [OracleSafe, oracleEq] using oracle

private theorem everyFnVarsNone_mem (expressions : List ClosLang.Exp)
    (safe : everyFnVarsNone expressions) (body : ClosLang.Exp) (member : body ∈ expressions) :
    everyFnVarsNone [body] := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [everyFnVarsNone] at safe
    rcases List.mem_cons.mp member with rfl | member
    · simpa [everyFnVarsNone] using safe.1
    · exact ih safe.2 member

private theorem updateCode_safe (lookup : Nat → Option (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp))
    (safe : ∀ key arity body, lookup key = some (arity, body) → everyFnVarsNone [body])
    (entriesSafe : ∀ entry ∈ entries, everyFnVarsNone [entry.2.2]) :
    ∀ key arity body, FUPDATE_LIST_HOL lookup entries key = some (arity, body) → everyFnVarsNone [body] := by
  induction entries generalizing lookup with
  | nil => simpa [FUPDATE_LIST_HOL] using safe
  | cons entry rest ih =>
    rw [FUPDATE_LIST_HOL_cons]
    apply ih
    · intro key arity body found
      by_cases same : key = entry.1
      · subst key
        simp [FUPDATE_HOL] at found
        have eq := found
        cases entry with
        | mk key payload =>
          cases payload with
          | mk storedArity storedBody =>
            simp only [Prod.mk.injEq] at eq
            obtain ⟨rfl, rfl⟩ := eq
            exact entriesSafe (key, storedArity, storedBody) (by simp)
      · apply safe key arity body
        simpa [FUPDATE_HOL, same] using found
    · intro e member
      exact entriesSafe e (by simp [member])

/-- A non-type-error installation retains safety of existing code, inserts
only safe oracle bodies, and advances to another safe oracle suffix. -/
theorem doInstall_preserves_safe {C F : Type} (values : List Value) (source next : State C F)
    (result : Result (List ClosLang.Exp) Value)
    (run : doInstall values source = (result, next)) (notType : result ≠ .err (.abort .typeError))
    (code : CodeSafe source) (oracle : OracleSafe source) : CodeSafe next ∧ OracleSafe next := by
  obtain ⟨_, _, _, _, config, expressions, auxiliary, _, _, _, _, oracleEntry, _, _, _, _, _, nextEq, _⟩ :=
    doInstall_nonType_parts values source next result run notType
  have bodies : everyFnVarsNone (auxiliary.map (fun (_, _, body) => body)) := by
    have h := (oracle 0).2
    simpa [oracleEntry] using h
  have entriesSafe : ∀ entry ∈ auxiliary, everyFnVarsNone [entry.2.2] := by
    intro entry member
    apply everyFnVarsNone_mem _ bodies entry.2.2
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [nextEq]
  constructor
  · intro key arity body found
    simp only [HolFiniteMapExact.lookup_updateListEq] at found
    exact updateCode_safe source.code.lookup auxiliary code entriesSafe key arity body found
  · intro index
    exact oracle (index + 1)

/-- Invalid installation requests leave the state unchanged. -/
theorem doInstall_typeError_state {C F : Type} (values : List Value) (source next : State C F)
    (run : doInstall values source = (.err (.abort .typeError), next)) : next = source := by
  unfold doInstall at run
  repeat' first | split at run | simp_all

/-- Installation preserves code and oracle safety for every result,
including rejected requests and timeouts. -/
theorem doInstall_preserves_safe_all {C F : Type} (values : List Value) (source next : State C F)
    (result : Result (List ClosLang.Exp) Value) (run : doInstall values source = (result, next))
    (code : CodeSafe source) (oracle : OracleSafe source) : CodeSafe next ∧ OracleSafe next := by
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have same := doInstall_typeError_state values source next run
    simpa [same] using And.intro code oracle
  · exact doInstall_preserves_safe values source next result run typeError code oracle

/-- An ordinary operation preserves safety when its arguments do. -/
theorem evaluate_ordinaryOp_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) (source : State C F)
    (argsIH : PreservesCodeOracleAt source args) :
    PreservesCodeOracleAt source [.op trace op args] := by
  intro env result next run code oracle
  rw [evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleSafe := argsIH env argsResult middle argsRun code oracle
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      exact middleSafe
    | val values =>
      dsimp only at run
      cases appRun : doApp op values.reverse middle with
      | err error =>
        rw [appRun] at run
        cases run
        exact middleSafe
      | val pair =>
        obtain ⟨value, final⟩ := pair
        rw [appRun] at run
        cases run
        exact doApp_preserves_safe op values.reverse middle next value appRun middleSafe.1 middleSafe.2

/-- Installation preserves safety when argument evaluation and the
dynamically installed program do. -/
theorem evaluate_install_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : PreservesCodeOracleAt source args)
    (programIH : ∀ program (state : State C F), state.clock < source.clock → PreservesCodeOracleAt state program) :
    PreservesCodeOracleAt source [.op trace .install args] := by
  intro env result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleSafe := argsIH env argsResult middle argsRun code oracle
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      exact middleSafe
    | val values =>
      dsimp only at run
      cases installRun : doInstall values.reverse middle with
      | mk installResult installed =>
        have installedSafe := doInstall_preserves_safe_all values.reverse middle installed installResult
          installRun middleSafe.1 middleSafe.2
        rw [installRun] at run
        cases installResult with
        | err error =>
          cases run
          exact installedSafe
        | val program =>
          dsimp only at run
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            have installedClock := doInstall_success_clock values.reverse middle installed program installRun
            have smaller : installed.clock < source.clock := by omega
            have finalSafe := programIH program installed smaller [] programResult final programRun installedSafe.1 installedSafe.2
            rw [programRun] at run
            cases programResult <;> cases run <;> exact finalSafe

/-- Evaluating an empty list or a variable leaves the code and oracle intact. -/
theorem evaluate_nil_preserves_safe {C F : Type} : PreservesCodeOracle (C := C) (F := F) [] := by
  intro env source result next run code oracle
  simp [evaluate] at run
  obtain ⟨_, rfl⟩ := run
  exact ⟨code, oracle⟩

theorem evaluate_var_preserves_safe {C F : Type} (trace : BackendCommon.Tra) (index : Nat) :
    PreservesCodeOracle (C := C) (F := F) [.var trace index] := by
  intro env source result next run code oracle
  simp only [evaluate] at run
  split at run <;> simp_all

/-- Sequencing preserves safety when both component evaluations do. -/
theorem evaluate_cons_preserves_safe_step {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (source : State C F) (firstIH : PreservesCodeOracleAt source [first])
    (restIH : ∀ state : State C F, state.clock ≤ source.clock → PreservesCodeOracleAt state (second :: rest)) :
    PreservesCodeOracleAt source (first :: second :: rest) := by
  intro env result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    have middleSafe := firstIH env firstResult middle firstRun code oracle
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [first] env source
      simpa [firstRun] using h
    rw [firstRun] at run
    cases firstResult with
    | err error => cases run; exact middleSafe
    | val values =>
      dsimp only at run
      cases restRun : evaluate (second :: rest) env middle with
      | mk restResult last =>
        have lastSafe := restIH middle middleClock env restResult last restRun middleSafe.1 middleSafe.2
        rw [restRun] at run
        cases restResult <;> cases run <;> exact lastSafe

/-- Raise expressions inherit safety preservation from their body. -/
theorem evaluate_raise_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : PreservesCodeOracleAt source [body]) :
    PreservesCodeOracleAt source [.raise trace body] := by
  intro env result next run code oracle
  rw [evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have middleSafe := bodyIH env bodyResult middle bodyRun code oracle
    rw [bodyRun] at run
    cases bodyResult <;> cases run <;> exact middleSafe

/-- Tick expressions only change the clock before evaluating their body. -/
theorem evaluate_tick_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : PreservesCodeOracleAt (decClock 1 source) [body]) :
    PreservesCodeOracleAt source [.tick trace body] := by
  intro env result next run code oracle
  by_cases zero : source.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨_, rfl⟩ := run
    exact ⟨code, oracle⟩
  · have bodyRun : evaluate [body] env (decClock 1 source) = (result, next) := by
      simpa [evaluate, zero] using run
    apply bodyIH env result next bodyRun
    · simpa [CodeSafe, decClock] using code
    · simpa [OracleSafe, decClock] using oracle

/-- Let expressions preserve safety through their bindings and body. -/
theorem evaluate_let_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (source : State C F)
    (bindingsIH : PreservesCodeOracleAt source bindings)
    (bodyIH : ∀ state : State C F, state.clock ≤ source.clock → PreservesCodeOracleAt state [body]) :
    PreservesCodeOracleAt source [.let trace bindings body] := by
  intro env result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate bindings env source with
  | mk bindingsResult middle =>
    have middleSafe := bindingsIH env bindingsResult middle bindingsRun code oracle
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le bindings env source
      simpa [bindingsRun] using h
    rw [bindingsRun] at run
    cases bindingsResult with
    | err error => cases run; exact middleSafe
    | val values => exact bodyIH middle middleClock (values ++ env) result next run middleSafe.1 middleSafe.2

/-- Exception handlers preserve safety through both the body and handler. -/
theorem evaluate_handle_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (source : State C F) (bodyIH : PreservesCodeOracleAt source [body])
    (handlerIH : ∀ state : State C F, state.clock ≤ source.clock → PreservesCodeOracleAt state [handler]) :
    PreservesCodeOracleAt source [.handle trace body handler] := by
  intro env result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have middleSafe := bodyIH env bodyResult middle bodyRun code oracle
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [body] env source
      simpa [bodyRun] using h
    rw [bodyRun] at run
    cases bodyResult with
    | val values => cases run; exact middleSafe
    | err error =>
      cases error with
      | abort reason => cases run; exact middleSafe
      | raise value => exact handlerIH middle middleClock (value :: env) result next run middleSafe.1 middleSafe.2

/-- Conditionals preserve safety along the evaluated condition and branch. -/
theorem evaluate_if_preserves_safe_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (source : State C F) (conditionIH : PreservesCodeOracleAt source [condition])
    (yesIH : ∀ state : State C F, state.clock ≤ source.clock → PreservesCodeOracleAt state [yes])
    (noIH : ∀ state : State C F, state.clock ≤ source.clock → PreservesCodeOracleAt state [no]) :
    PreservesCodeOracleAt source [.ifThenElse trace condition yes no] := by
  intro env result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases testRun : evaluate [condition] env source with
  | mk testResult middle =>
    have middleSafe := conditionIH env testResult middle testRun code oracle
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [condition] env source
      simpa [testRun] using h
    rw [testRun] at run
    cases testResult with
    | err error => cases run; exact middleSafe
    | val values =>
      dsimp only at run
      split at run
      · cases run; exact middleSafe
      · exact yesIH middle middleClock env result next run middleSafe.1 middleSafe.2
      · exact noIH middle middleClock env result next run middleSafe.1 middleSafe.2

/-- Constructing a closure leaves code and oracle untouched. -/
theorem evaluate_fn_preserves_safe {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp) :
    PreservesCodeOracle (C := C) (F := F) [.fn name location selected arity body] := by
  intro env source result next run code oracle
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run <;> simp_all

/-- Recursive closure construction either fails without changing state or
evaluates the body with an extended environment. -/
theorem evaluate_letrec_preserves_safe_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (source : State C F) (bodyIH : PreservesCodeOracleAt source [body]) :
    PreservesCodeOracleAt source [.letrec names location selected functions body] := by
  intro env result next run code oracle
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run
  all_goals try (simp_all; done)
  all_goals exact bodyIH _ result next run code oracle
end Flapjack.Compiler.Backend.ClosAnnotate
