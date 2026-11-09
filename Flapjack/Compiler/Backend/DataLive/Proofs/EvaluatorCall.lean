import Flapjack.Compiler.Backend.DataLive.Proofs.EvaluatorForce

/-! Same-program call simulation across related call stacks. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Same-program non-tail call simulation at a fixed clock, conditional on
simulation of all evaluations at smaller clocks. -/
theorem evaluatorSimulation_nonTailCall_at {C F : Type} (returns : List Nat) (names : NumSet)
    (dest : Option Nat) (arguments : List Nat) (handler : Option (Nat × DataLang.Prog))
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.call (some (returns, names)) dest arguments handler) source = (result, sourceNext))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.call (some (returns, names)) dest arguments handler) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  have readEq : DataSem.getVars arguments source.locals = DataSem.getVars arguments target.locals := by rw [sameLocals]
  cases read : DataSem.getVars arguments source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some values =>
    have targetRead : DataSem.getVars arguments target.locals = some values := by rw [← readEq, read]
    have findEq : findCode dest values target.code target.stackFrameSizes = findCode dest values source.code source.stackFrameSizes := by
      rw [← related.1, ← related.2.2.2.2.2.2.2.2.2.2.2.2.1]
    cases found : findCode dest values source.code source.stackFrameSizes with
    | none =>
      simp [DataSem.evaluate, read, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      have targetFound : findCode dest values target.code target.stackFrameSizes = some (args, body, size) := by rw [findEq, found]
      by_cases unique : returns.Nodup
      · cases cut : cutEnv names source.locals with
        | none =>
          simp [DataSem.evaluate, read, found, unique, cut] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
        | some env =>
          have targetCut : cutEnv names target.locals = some env := by rw [← sameLocals, cut]
          have savedRel : stateRel { source with locals := env } { target with locals := env } .ln := by
            rcases related with ⟨code, clock, space, ffi, refs, global, handlerEq, stack, compiler, oracle, stamps, limits, frames, _⟩
            exact ⟨code, clock, space, ffi, refs, global, handlerEq, stack, compiler, oracle, stamps, limits, frames, by simp⟩
          let sourceEntry := DataSem.callEnv args size (pushEnv env handler.isSome (decClock source))
          let targetEntry := DataSem.callEnv args size (pushEnv env handler.isSome (decClock target))
          have entryRel := stateRel_nonTailEntry source target .ln args size env env handler.isSome related
          by_cases zero : source.clock = 0
          · have targetZero : target.clock = 0 := by rw [← related.2.1, zero]
            simp [DataSem.evaluate, read, found, unique, cut, zero] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨{ targetEntry with stack := [], locals := .ln }, ?_, ?_, by simp⟩
            · simp [DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetZero, targetEntry]
            · simpa [sourceEntry, targetEntry] using stateRel_clearStackLocals sourceEntry targetEntry .ln entryRel.1
          · have targetNonzero : target.clock ≠ 0 := by rw [← related.2.1]; exact zero
            have entryException : exceptionRel sourceEntry targetEntry := by
              cases handler with
              | none => exact exceptionRel_nonTailEntry_noHandler source target .ln args size env env related exception
              | some pair => exact exceptionRel_nonTailEntry_handler source target .ln args size env env related
            have smaller : sourceEntry.clock < source.clock := by
              cases handler <;> simp [sourceEntry, DataSem.callEnv, pushEnv, decClock] <;> omega
            cases called : DataSem.evaluate body sourceEntry with
            | mk outcome last =>
              have sourceClamped : fixClock sourceEntry (DataSem.evaluate body sourceEntry) = (outcome, last) := by
                rw [fixClock_evaluate, called]
              simp only [sourceEntry] at sourceClamped
              cases outcome with
              | none =>
                simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped] at run
                obtain ⟨rfl, rfl⟩ := run
                exact False.elim (notType rfl)
              | some outcome =>
                cases outcome with
                | val returned =>
                  by_cases lengths : returned.length = returns.length
                  · obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                      bodyIH body sourceEntry targetEntry last (some (.val returned)) smaller entryRel.1 entryRel.2 entryException (by simp) called
                    have sourceControl := evaluate_stackResult body sourceEntry last (some (.val returned)) called
                    have targetControl := evaluate_stackResult body targetEntry targetLast (some (.val returned)) targetRun
                    obtain ⟨sourcePop, targetPop, sourcePopRun, targetPopRun, popRel⟩ :=
                      stateRel_popNonTail source target last targetLast args size env env handler.isSome .ln
                        lastRel savedRel sourceControl.1 sourceControl.2 targetControl.1 targetControl.2
                    have sourcePopLocals := popNonTail_locals source last sourcePop args size env handler.isSome sourceControl.1 sourceControl.2 sourcePopRun
                    have targetPopLocals := popNonTail_locals target targetLast targetPop args size env handler.isSome targetControl.1 targetControl.2 targetPopRun
                    simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped, lengths, sourcePopRun] at run
                    obtain ⟨rfl, rfl⟩ := run
                    have targetClamped : fixClock targetEntry (DataSem.evaluate body targetEntry) = (some (.val returned), targetLast) := by
                      rw [fixClock_evaluate, targetRun]
                    simp only [targetEntry] at targetClamped
                    have afterRel : stateRel (setVars returns returned sourcePop) (setVars returns returned targetPop) .ln :=
                      stateRel_setVars sourcePop targetPop .ln returns returned lengths
                        (stateRel_of_sameLocals sourcePop targetPop _ popRel (sourcePopLocals.trans targetPopLocals.symm))
                    refine ⟨setVars returns returned targetPop, ?_, afterRel, ?_⟩
                    · simp [DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped, lengths, targetPopRun]
                    · intro _
                      simp [setVars, sourcePopLocals, targetPopLocals]
                  · simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped, lengths] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact False.elim (notType rfl)
                | err error =>
                  cases error with
                  | abort reason =>
                    simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped] at run
                    obtain ⟨rfl, rfl⟩ := run
                    obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                      bodyIH body sourceEntry targetEntry last _ smaller entryRel.1 entryRel.2 entryException notType called
                    have targetClamped := targetRun
                    rw [← fixClock_evaluate body targetEntry] at targetClamped
                    simp only [targetEntry] at targetClamped
                    exact ⟨targetLast, by simp [DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped], lastRel, by simp⟩
                  | raise value =>
                    cases handler with
                    | none =>
                      simp only [Option.isSome] at sourceClamped
                      simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped] at run
                      obtain ⟨rfl, rfl⟩ := run
                      obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                        bodyIH body sourceEntry targetEntry last (some (.err (.raise value))) smaller entryRel.1 entryRel.2 entryException (by simp) called
                      have targetClamped := targetRun
                      rw [← fixClock_evaluate body targetEntry] at targetClamped
                      simp only [targetEntry, Option.isSome] at targetClamped
                      exact ⟨targetLast, by simp [DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped], lastRel, by simp⟩
                    | some pair =>
                      obtain ⟨name, handlerBody⟩ := pair
                      simp only [Option.isSome] at sourceClamped
                      have handlerRun : DataSem.evaluate handlerBody (setVar name value last) = (result, sourceNext) := by
                        simpa [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped] using run
                      obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                        bodyIH body sourceEntry targetEntry last (some (.err (.raise value))) smaller entryRel.1 entryRel.2 entryException (by simp) called
                      obtain ⟨restored, restoredException⟩ :=
                        handlerEntry_afterRaise source target last targetLast args size env env .ln body value savedRel lastRel exception called targetRun
                      have sourceControl := evaluate_stackResult body sourceEntry last (some (.err (.raise value))) called
                      have targetControl := evaluate_stackResult body targetEntry targetLast (some (.err (.raise value))) targetRun
                      obtain ⟨sourceJump, sourceJumpRun, _, _, sourceLocals⟩ := sourceControl
                      obtain ⟨targetJump, targetJumpRun, _, _, targetLocals⟩ := targetControl
                      have sourceJumpEq := Option.some.inj (sourceJumpRun.symm.trans (jumpExc_callEnv_push_handler source args size env))
                      have targetJumpEq := Option.some.inj (targetJumpRun.symm.trans (jumpExc_callEnv_push_handler target args size env))
                      have sourceRestored : last.locals = env := by simpa [sourceJumpEq] using sourceLocals
                      have targetRestored : targetLast.locals = env := by simpa [targetJumpEq] using targetLocals
                      have sameLast : last.locals = targetLast.locals := sourceRestored.trans targetRestored.symm
                      have handlerRel := stateRel_setVar last targetLast .ln name value (by simpa [sptDelete] using restored)
                      have handlerException : exceptionRel (setVar name value last) (setVar name value targetLast) := by
                        apply exceptionRel_after last targetLast _ _ _ handlerRel restoredException <;> rfl
                      have lastClock : (setVar name value last).clock < source.clock := by
                        have bound := evaluate_clock_le body sourceEntry
                        rw [called] at bound
                        simpa [setVar] using Nat.lt_of_le_of_lt bound smaller
                      obtain ⟨targetNext, targetHandlerRun, finalRel, finalLocals⟩ :=
                        bodyIH handlerBody (setVar name value last) (setVar name value targetLast) sourceNext result lastClock handlerRel
                          (by simp [setVar, sameLast]) handlerException notType handlerRun
                      have targetClamped := targetRun
                      rw [← fixClock_evaluate body targetEntry] at targetClamped
                      simp only [targetEntry, Option.isSome] at targetClamped
                      refine ⟨targetNext, ?_, finalRel, finalLocals⟩
                      simpa [DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped] using targetHandlerRun
      · simp [DataSem.evaluate, read, found, unique] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)

/-- All same-program call cases follow from the smaller-clock evaluator
simulation. -/
theorem evaluatorSimulation_call_at {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (arguments : List Nat) (handler : Option (Nat × DataLang.Prog))
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.call ret dest arguments handler) source = (result, sourceNext))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.call ret dest arguments handler) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  cases ret with
  | none => exact evaluatorSimulation_tailCall_anyHandler_at dest arguments handler source target sourceNext result related sameLocals exception notType run bodyIH
  | some pair =>
    obtain ⟨returns, names⟩ := pair
    exact evaluatorSimulation_nonTailCall_at returns names dest arguments handler source target sourceNext result related sameLocals exception notType run bodyIH

end Flapjack.Compiler.Backend.DataLive
