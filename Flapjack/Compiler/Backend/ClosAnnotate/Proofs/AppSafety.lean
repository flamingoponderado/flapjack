import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstallSafety
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Code and oracle safety through indirect and direct closure application. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Safety preservation for application states below a clock bound. -/
def AppPreservesBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (location : Option Nat) (function : Value) (args : List Value)
    (source next : State C F) (result : Result (List Value) Value),
    source.clock < clock → evaluateApp location function args source = (result, next) →
    CodeSafe source → OracleSafe source → CodeSafe next ∧ OracleSafe next

/-- One closure application preserves safety assuming its recursive body and
subsequent application do so at strictly smaller clocks. -/
theorem evaluateApp_preserves_safe_step {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (source next : State C F) (result : Result (List Value) Value)
    (run : evaluateApp location function args source = (result, next)) (code : CodeSafe source)
    (oracle : OracleSafe source)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (start final : State C F)
      (result : Result (List Value) Value), start.clock < source.clock →
      evaluate [body] env start = (result, final) → CodeSafe start → OracleSafe start →
      CodeSafe final ∧ OracleSafe final)
    (appIH : AppPreservesBelow (C := C) (F := F) source.clock) : CodeSafe next ∧ OracleSafe next := by
  cases args with
  | nil => simp [evaluateApp] at run; obtain ⟨_, rfl⟩ := run; exact ⟨code, oracle⟩
  | cons first rest =>
    rw [evaluateApp] at run
    cases found : destClosure source.maxApp location function (first :: rest) with
    | none =>
      rw [found] at run
      cases run
      exact ⟨code, oracle⟩
    | some kind =>
      rw [found] at run
      cases kind with
      | partialApp value =>
        dsimp only at run
        split at run <;> simp [decClock] at run <;>
          obtain ⟨_, rfl⟩ := run <;> simpa [decClock, CodeSafe, OracleSafe] using And.intro code oracle
      | fullApp body env remaining =>
        dsimp only at run
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost :=
          Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ found)
        split at run
        · simp at run
          obtain ⟨_, rfl⟩ := run
          simpa [CodeSafe, OracleSafe] using And.intro code oracle
        · rename_i enough
          have smaller : (decClock cost source).clock < source.clock := by simp [decClock]; omega
          have startCode : CodeSafe (decClock cost source) := by simpa [CodeSafe, decClock] using code
          have startOracle : OracleSafe (decClock cost source) := by simpa [OracleSafe, decClock] using oracle
          rw [fixClock_evaluate] at run
          cases bodyRun : evaluate [body] env (decClock cost source) with
          | mk bodyResult middle =>
            have middleSafe := bodyIH body env (decClock cost source) middle bodyResult
              smaller bodyRun startCode startOracle
            have clockLe : middle.clock ≤ (decClock cost source).clock := by
              have h := evaluate_clock_le [body] env (decClock cost source)
              simpa [bodyRun] using h
            rw [bodyRun] at run
            cases bodyResult with
            | err error => cases run; exact middleSafe
            | val values =>
              cases values with
              | nil => cases run; exact middleSafe
              | cons value tail =>
                cases tail with
                | nil => exact appIH location value remaining middle next result (by omega) run middleSafe.1 middleSafe.2
                | cons other tail => cases run; exact middleSafe

/-- Application expressions preserve safety through arguments, the function
expression, and closure application. -/
theorem evaluate_app_preserves_safe {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (argsIH : PreservesCodeOracle (C := C) (F := F) args)
    (functionIH : PreservesCodeOracle (C := C) (F := F) [function])
    (appIH : ∀ clock, AppPreservesBelow (C := C) (F := F) clock) :
    PreservesCodeOracle (C := C) (F := F) [.app trace location function args] := by
  intro env source result next run code oracle
  cases args with
  | nil => simp [evaluate] at run; obtain ⟨_, rfl⟩ := run; exact ⟨code, oracle⟩
  | cons first rest =>
    rw [evaluate, fixClock_evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      have middleSafe := argsIH env source argsResult middle argsRun code oracle
      rw [argsRun] at run
      cases argsResult with
      | err error => cases run; exact middleSafe
      | val values =>
        rw [fixClock_evaluate] at run
        cases functionRun : evaluate [function] env middle with
        | mk functionResult last =>
          have lastSafe := functionIH env middle functionResult last functionRun middleSafe.1 middleSafe.2
          rw [functionRun] at run
          cases functionResult with
          | err error => cases run; exact lastSafe
          | val functions =>
            exact appIH (last.clock + 1) location _ values last next result (by omega) run lastSafe.1 lastSafe.2

/-- Direct calls preserve safety through their arguments and selected body. -/
theorem evaluate_call_preserves_safe {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (argsIH : PreservesCodeOracle (C := C) (F := F) args)
    (bodyIH : ∀ body, PreservesCodeOracle (C := C) (F := F) [body]) :
    PreservesCodeOracle (C := C) (F := F) [.call trace ticks location args] := by
  intro env source result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleSafe := argsIH env source argsResult middle argsRun code oracle
    rw [argsRun] at run
    cases argsResult with
    | err error => cases run; exact middleSafe
    | val values =>
      dsimp only at run
      cases found : findCode location values middle.code with
      | none => rw [found] at run; cases run; exact middleSafe
      | some entry =>
        obtain ⟨bodyEnv, body⟩ := entry
        rw [found] at run
        dsimp only at run
        split at run
        · simp at run
          obtain ⟨_, rfl⟩ := run
          simpa [CodeSafe, OracleSafe] using middleSafe
        · apply bodyIH body bodyEnv (decClock (ticks + 1) middle) result next run
          · simpa [CodeSafe, decClock] using middleSafe.1
          · simpa [OracleSafe, decClock] using middleSafe.2

/-- Forcing a thunk changes at most its reference store after evaluating the
thunk body, so code and oracle safety are retained. -/
theorem evaluate_force_preserves_safe {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (argsIH : PreservesCodeOracle (C := C) (F := F) args)
    (forceIH : PreservesCodeOracle (C := C) (F := F) [appUnit (.var .none 0)]) :
    PreservesCodeOracle (C := C) (F := F) [.op trace (.thunkOp .forceThunk) args] := by
  intro env source result next run code oracle
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleSafe := argsIH env source argsResult middle argsRun code oracle
    rw [argsRun] at run
    cases argsResult with
    | err error => cases run; exact middleSafe
    | val values =>
      dsimp only at run
      cases thunk : destThunk values middle.refs with
      | badRef => rw [thunk] at run; cases run; exact middleSafe
      | notThunk => rw [thunk] at run; cases run; exact middleSafe
      | isThunk mode value =>
        rw [thunk] at run
        cases mode with
        | evaluated => cases run; exact middleSafe
        | notEvaluated =>
          dsimp only at run
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
          | mk forceResult last =>
            have lastSafe := forceIH [value] middle forceResult last forceRun middleSafe.1 middleSafe.2
            rw [forceRun] at run
            cases forceResult with
            | err error => cases run; exact lastSafe
            | val forced =>
              dsimp only at run
              cases updated : updateThunk values last.refs forced with
              | none => rw [updated] at run; cases run; exact lastSafe
              | some refs =>
                rw [updated] at run
                cases run
                simpa [CodeSafe, OracleSafe] using lastSafe

end Flapjack.Compiler.Backend.ClosAnnotate
