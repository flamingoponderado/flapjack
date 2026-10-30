import Flapjack.Compiler.Backend.Semantics.ClosSem.Events
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

/-! Event-prefix steps for the proof-side closure evaluator. The evaluator
and its carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A non-timeout evaluation has the same event trace at any larger clock. -/
theorem evaluate_addClock_ioEvents_of_notTimeout {C F : Type} (expressions : List ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (run : evaluate expressions env state = (result, next)) (notTimeout : result ≠ .err (.abort .timeoutError)) :
    (evaluate expressions env state).2.ffi.ioEvents =
      (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  have shifted := evaluate_addClock.1 expressions env state next result extra run notTimeout
  simp [run, shifted]

/-- A non-timeout closure application has the same trace at any larger clock. -/
theorem evaluateApp_addClock_ioEvents_of_notTimeout {C F : Type} (location : Option Nat)
    (function : Value) (args : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (run : evaluateApp location function args state = (result, next)) (notTimeout : result ≠ .err (.abort .timeoutError)) :
    (evaluateApp location function args state).2.ffi.ioEvents =
      (evaluateApp location function args { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  have shifted := evaluate_addClock.2 location function args state next result extra run notTimeout
  simp [run, shifted]

/-- Sequential evaluation extends the initial event trace when its head
and tail do. -/
theorem evaluate_cons_ioEvents_step {C F : Type} (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (env : List Value) (state final : State C F) (result : Result (List Value) Value)
    (headIH : ∀ (last : State C F) (headResult : Result (List Value) Value),
      evaluate [head] env state = (headResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (tailIH : ∀ (start last : State C F) (tailResult : Result (List Value) Value),
      start.clock ≤ state.clock → evaluate tail env start = (tailResult, last) →
      start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate (head :: tail) env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  cases headRun : evaluate [head] env state with
  | mk headResult last =>
    have headPrefix := headIH last headResult headRun
    cases headResult with
    | err error =>
      rw [ClosProps.evaluate_cons_error head tail env state last error headRun] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact headPrefix
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value head env state last values headRun
      have bound : last.clock ≤ state.clock := by
        have clock := evaluate_clock_le [head] env state
        simpa [headRun] using clock
      rw [ClosProps.evaluate_cons_value head tail env state last value headRun] at run
      cases tailRun : evaluate tail env last with
      | mk tailResult tailFinal =>
        rw [tailRun] at run
        have tailPrefix := tailIH last tailFinal tailResult bound tailRun
        cases tailResult <;> simp at run
        all_goals rcases run with ⟨rfl, rfl⟩
        all_goals exact headPrefix.trans tailPrefix

/-- Ordinary operations extend the trace when evaluation of their arguments
does. -/
theorem evaluate_ordinaryOp_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value)
    (state final : State C F) (result : Result (List Value) Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (last : State C F) (argResult : Result (List Value) Value),
      evaluate args env state = (argResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.op trace op args] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce] at run
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    rw [argsRun] at run
    have argsPrefix := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact argsPrefix
    | val arguments =>
      cases appRun : doApp op arguments.reverse last with
      | err error =>
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact argsPrefix
      | val pair =>
        rcases pair with ⟨value, next⟩
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact argsPrefix.trans (doApp_ioEvents_prefix op arguments.reverse last next value appRun)

/-- Installation extends the trace when its argument evaluation and the
installed program's evaluation do. -/
theorem evaluate_install_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state final : State C F)
    (result : Result (List Value) Value)
    (argsIH : ∀ (last : State C F) (argResult : Result (List Value) Value),
      evaluate args env state = (argResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (programIH : ∀ (program : List ClosLang.Exp) (start last : State C F) (programResult : Result (List Value) Value),
      start.clock < state.clock → evaluate program [] start = (programResult, last) →
      start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.op trace .install args] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [argsRun] at run
    have argsPrefix := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact argsPrefix
    | val arguments =>
      dsimp only at run
      cases installRun : doInstall arguments.reverse last with
      | mk installResult installed =>
        rw [installRun] at run
        have ffiEq := doInstall_ffi arguments.reverse last installed installResult installRun
        cases installResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          simpa [ffiEq] using argsPrefix
        | val program =>
          dsimp only at run
          have consumed := doInstall_success_clock arguments.reverse last installed program installRun
          cases programRun : evaluate program [] installed with
          | mk programResult lastFinal =>
            rw [programRun] at run
            have programPrefix := programIH program installed lastFinal programResult (by omega) programRun
            have before : state.ffi.ioEvents <+: installed.ffi.ioEvents := by simpa [ffiEq] using argsPrefix
            cases programResult <;> simp at run
            all_goals rcases run with ⟨rfl, rfl⟩
            all_goals exact before.trans programPrefix

/-- Forcing a thunk extends the trace when its arguments and forced
computation do. -/
theorem evaluate_force_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state final : State C F)
    (result : Result (List Value) Value)
    (argsIH : ∀ (last : State C F) (argResult : Result (List Value) Value),
      evaluate args env state = (argResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (forceIH : ∀ (value : Value) (start last : State C F) (forceResult : Result (List Value) Value),
      start.clock ≤ state.clock → evaluate [appUnit (.var .none 0)] [value] start = (forceResult, last) →
      start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.op trace (.thunkOp .forceThunk) args] env state = (result, final)) :
    state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [argsRun] at run
    have argsPrefix := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact argsPrefix
    | val arguments =>
      dsimp only at run
      cases inspected : destThunk arguments last.refs with
      | badRef | notThunk =>
        simp [inspected] at run
        rcases run with ⟨rfl, rfl⟩
        exact argsPrefix
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          simp [inspected] at run
          rcases run with ⟨rfl, rfl⟩
          exact argsPrefix
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] last with
          | mk forceResult forceFinal =>
            rw [forceRun] at run
            have forcePrefix := forceIH value last forceFinal forceResult bound forceRun
            cases forceResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              exact argsPrefix.trans forcePrefix
            | val forced =>
              dsimp only at run
              cases updated : updateThunk arguments forceFinal.refs forced with
              | none =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                exact argsPrefix.trans forcePrefix
              | some refs =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                exact argsPrefix.trans forcePrefix

end Flapjack.Compiler.Backend.ClosSem
