import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateEventsClock

/-! Call and continuation trace facts for BVI clock comparisons. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value findCode)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- When the call is well-formed, its argument trace is a prefix of the
complete call trace, including any invoked exception handler. -/
theorem evaluate_call_args_ioEvents_prefix {C F : Type} (ticks : Nat)
    (dest : Option Nat) (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (env : List Value) (state : BviState C F)
    (legal : (dest.isNone && handler.isSome) = false) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.call ticks dest args handler] env state).2.ffi.ioEvents := by
  rw [evaluate]
  simp only [legal, Bool.false_eq_true, ↓reduceIte]
  rw [fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error => simp
    | val values =>
      dsimp only
      cases found : findCode dest values last.code with
      | none => simp
      | some entry =>
        obtain ⟨selected, body⟩ := entry
        dsimp only
        split
        · simp
        · rw [fixClock_evaluate]
          have bodyPrefix := evaluate_ioEvents_prefix [body] selected (decClock (ticks + 1) last)
          cases bodyRun : evaluate [body] selected (decClock (ticks + 1) last) with
          | mk bodyResult called =>
            simp only [bodyRun, eventGrowth] at bodyPrefix
            change last.ffi.ioEvents <+: called.ffi.ioEvents at bodyPrefix
            cases bodyResult with
            | val values => simpa using bodyPrefix
            | err error =>
              cases error with
              | abort reason => simpa using bodyPrefix
              | raise payload =>
                cases payload with
                | ret values => simpa using bodyPrefix
                | exn value =>
                  cases handler with
                  | none => simpa using bodyPrefix
                  | some handler =>
                    dsimp only
                    have handlerPrefix := evaluate_ioEvents_prefix [handler] (value :: env) called
                    cases handlerRun : evaluate [handler] (value :: env) called with
                    | mk result final =>
                      simp only [handlerRun, eventGrowth] at handlerPrefix
                      cases result <;> simp_all
                      all_goals repeat' (split <;> simp_all)
                      all_goals exact bodyPrefix.trans handlerPrefix

/-- The arguments of a let-call form a prefix of its entire trace, including
the selected callee and any continuation after a returned value. -/
theorem evaluate_letCall_args_ioEvents_prefix {C F : Type} (rets ticks dest : Nat)
    (args : List Bvi.Exp) (body : Bvi.Exp) (env : List Value) (state : BviState C F) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.letCall rets ticks dest args body] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error => simp
    | val values =>
      dsimp only
      cases found : findCode (some dest) values last.code with
      | none => simp
      | some entry =>
        obtain ⟨selected, callee⟩ := entry
        dsimp only
        split
        · simp
        · rw [fixClock_evaluate]
          have calleePrefix := evaluate_ioEvents_prefix [callee] selected (decClock (ticks + 1) last)
          cases calleeRun : evaluate [callee] selected (decClock (ticks + 1) last) with
          | mk calleeResult called =>
            simp only [calleeRun, eventGrowth] at calleePrefix
            change last.ffi.ioEvents <+: called.ffi.ioEvents at calleePrefix
            cases calleeResult with
            | val values => simpa using calleePrefix
            | err error =>
              cases error with
              | abort reason => simpa using calleePrefix
              | raise payload =>
                cases payload with
                | exn value => simpa using calleePrefix
                | ret values =>
                  dsimp only
                  split
                  · have continuationPrefix := evaluate_ioEvents_prefix [body] (values ++ env) called
                    exact calleePrefix.trans continuationPrefix
                  · exact calleePrefix

/-- A direct call is trace-monotone when its arguments and selected code
body are trace-monotone. -/
theorem evaluate_directCall_addClock_ioEvents_step {C F : Type} (ticks : Nat) (location : Option Nat) (args : List Bvi.Exp) (env : List Value) (state : BviState C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (bodyIH : ∀ (body : Bvi.Exp) (bodyEnv : List Value) (start : BviState C F), start.clock < state.clock →
      (evaluate [body] bodyEnv start).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.call ticks location args none] env state).2.ffi.ioEvents <+:
      (evaluate [.call ticks location args none] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.call ticks location args none] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false] at sourceRun
      cases argsRun : evaluate args env state with
      | mk argResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le args env state
          simpa [argsRun] using clock
        rw [argsRun] at sourceRun
        cases argResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have argsPrefix : last.ffi.ioEvents <+:
              (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by simpa [argsRun] using argsIH
          exact argsPrefix.trans (evaluate_call_args_ioEvents_prefix ticks location args none env
            { state with clock := state.clock + extra } (by simp))
        | val arguments =>
          have shiftedArgs := evaluate_addClock args env state last (.val arguments) extra argsRun (by simp)
          dsimp only at sourceRun
          cases found : findCode location arguments last.code with
          | none => simp [found] at sourceRun
          | some entry =>
            rcases entry with ⟨bodyEnv, body⟩
            rw [found] at sourceRun
            dsimp only at sourceRun
            by_cases short : last.clock < ticks + 1
            · rw [if_pos short] at sourceRun
              simp at sourceRun
              rcases sourceRun with ⟨_, rfl⟩
              have argsPrefix : last.ffi.ioEvents <+:
                  (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by simpa [argsRun] using argsIH
              exact argsPrefix.trans (evaluate_call_args_ioEvents_prefix ticks location args none env
                { state with clock := state.clock + extra } (by simp))
            · rw [if_neg short] at sourceRun
              have smaller : (decClock (ticks + 1) last).clock < state.clock := by simp [decClock]; omega
              have compare := bodyIH body bodyEnv (decClock (ticks + 1) last) smaller
              rw [fixClock_evaluate] at sourceRun
              cases bodyRun : evaluate [body] bodyEnv (decClock (ticks + 1) last) with
              | mk bodyResult bodyNext =>
               cases bodyResult with
               | val values => simp [bodyRun] at sourceRun
               | err error =>
                cases error with
                | raise payload => cases payload <;> simp [bodyRun] at sourceRun
                | abort reason =>
                 cases reason with
                 | typeError => simp [bodyRun] at sourceRun
                 | ffiError event => simp [bodyRun] at sourceRun
                 | timeoutError =>
                  simp [bodyRun] at sourceRun
                  subst final
                  simp only [bodyRun] at compare
                  have shifted : decClock (ticks + 1) { last with clock := last.clock + extra } =
                  { decClock (ticks + 1) last with clock := (decClock (ticks + 1) last).clock + extra } := by
                    simp only [decClock]
                    congr 1
                    omega
                  rw [evaluate, fixClock_evaluate, shiftedArgs]
                  simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false]
                  rw [found]
                  dsimp only
                  rw [if_neg (by omega), shifted, fixClock_evaluate]
                  cases targetRun : evaluate [body] bodyEnv { decClock (ticks + 1) last with
                      clock := (decClock (ticks + 1) last).clock + extra } with
                  | mk targetResult targetNext =>
                    cases targetResult <;> simp_all
                    all_goals repeat' (split <;> simp_all)
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.call ticks location args none] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]



end Flapjack.Compiler.Backend.BviProps
