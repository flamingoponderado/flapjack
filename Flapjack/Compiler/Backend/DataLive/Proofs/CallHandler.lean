module

public import Flapjack.Compiler.Backend.DataLive.Proofs.CallNonTail

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Exception-handler entry for data liveness. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Once matching callees raise to their fresh handler frames, the handler
simulation applies using the restored live locals and exception context.
This is auxiliary infrastructure, not the complete HOL call case. -/
theorem handlerSimulation_afterRaise {C F : Type}
    (source target sourceLast targetLast sourceNext : State C F)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value)
    (body handler : DataLang.Prog) (name : Nat) (value : DataSem.Value) (live : NumSet)
    (result : Option (Result (List DataSem.Value) DataSem.Value))
    (savedRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv }
      (sptDelete name (compile handler live).2))
    (lastRel : stateRel sourceLast targetLast .ln) (exception : exceptionRel source target)
    (sourceRun : DataSem.evaluate body (DataSem.callEnv args size (pushEnv sourceEnv true (decClock source))) =
      (some (.err (.raise value)), sourceLast))
    (targetRun : DataSem.evaluate body (DataSem.callEnv args size (pushEnv targetEnv true (decClock target))) =
      (some (.err (.raise value)), targetLast))
    (handlerRun : DataSem.evaluate handler (setVar name value sourceLast) = (result, sourceNext))
    (notType : result ≠ some (.err (.abort .typeError)))
    (handlerIH : simulationFor (C := C) (F := F) handler live) :
    ∃ targetNext, DataSem.evaluate (compile handler live).1 (setVar name value targetLast) = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  obtain ⟨restored, restoredException⟩ :=
    handlerEntry_afterRaise source target sourceLast targetLast args size sourceEnv targetEnv
      (sptDelete name (compile handler live).2) body value savedRel lastRel exception sourceRun targetRun
  have handlerRel := stateRel_setVar sourceLast targetLast (compile handler live).2 name value restored
  have handlerException : exceptionRel (setVar name value sourceLast) (setVar name value targetLast) := by
    apply exceptionRel_after sourceLast targetLast _ _ _ handlerRel restoredException <;> rfl
  exact handlerIH _ _ result sourceNext handlerRun handlerRel notType handlerException

/-- A non-tail call with a handler is simulated given the handler's liveness
simulation and the smaller-clock same-program evaluator simulation. The
latter remains an open prerequisite of the full pass correctness proof. -/
theorem call_nonTail_handler_correct {C F : Type} (returns : List Nat) (names : NumSet)
    (dest : Option Nat) (arguments : List Nat) (name : Nat) (handler : DataLang.Prog) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate (.call (some (returns, names)) dest arguments (some (name, handler))) source = (result, sourceNext))
    (related : stateRel source target (compile (.call (some (returns, names)) dest arguments (some (name, handler))) live).2)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock)
    (handlerIH : simulationFor (C := C) (F := F) handler live) :
    ∃ targetNext, DataSem.evaluate (compile (.call (some (returns, names)) dest arguments (some (name, handler))) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  let savedLive := sptUnion (sptListDelete returns live) (sptDelete name (compile handler live).2)
  have initial : stateRel source target (sptListInsert arguments (sptInter names savedLive)) := by
    simpa [compile, savedLive] using related
  have readEq := stateRel_getVars_listInsert source target arguments (sptInter names savedLive) initial
  have cutRel : stateRel source target (sptInter names savedLive) :=
    stateRel_mono source target _ _ initial (fun key member => (mem_listInsert arguments _ key).2 (Or.inr member))
  cases read : DataSem.getVars arguments source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some values =>
    have targetRead : DataSem.getVars arguments target.locals = some values := by rw [← readEq, read]
    have findEq : findCode dest values target.code target.stackFrameSizes =
        findCode dest values source.code source.stackFrameSizes := by
      rw [← initial.1, ← initial.2.2.2.2.2.2.2.2.2.2.2.2.1]
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
        | some sourceEnv =>
          obtain ⟨targetEnv, targetCut, savedLocals⟩ := cutEnv_inter_related source target names savedLive cutRel sourceEnv cut
          have savedRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv } savedLive := by
            rcases initial with ⟨code, clock, space, ffi, refEq, global, handlerEq, stack, compiler, oracle, stamps, limits, frames, _⟩
            exact ⟨code, clock, space, ffi, refEq, global, handlerEq, stack, compiler, oracle, stamps, limits, frames, savedLocals⟩
          have returnRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv } (sptListDelete returns live) :=
            stateRel_mono _ _ savedLive _ savedRel (fun key member =>
              (sptMem_sptUnion _ _ key).2 (Or.inl member))
          have handlerRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv } (sptDelete name (compile handler live).2) :=
            stateRel_mono _ _ savedLive _ savedRel (fun key member =>
              (sptMem_sptUnion _ _ key).2 (Or.inr member))
          let sourceEntry := DataSem.callEnv args size (pushEnv sourceEnv true (decClock source))
          let targetEntry := DataSem.callEnv args size (pushEnv targetEnv true (decClock target))
          have entryRel := stateRel_nonTailEntry source target _ args size sourceEnv targetEnv true initial
          by_cases zero : source.clock = 0
          · have targetZero : target.clock = 0 := by rw [← initial.2.1, zero]
            simp [DataSem.evaluate, read, found, unique, cut, zero] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨{ targetEntry with stack := [], locals := .ln }, ?_, ?_⟩
            · simp [compile, savedLive, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetZero, targetEntry]
            · simpa [postLive, sourceEntry, targetEntry] using
                stateRel_clearStackLocals sourceEntry targetEntry .ln entryRel.1
          · have targetNonzero : target.clock ≠ 0 := by rw [← initial.2.1]; exact zero
            have entryException := exceptionRel_nonTailEntry_handler source target _ args size sourceEnv targetEnv initial
            have smaller : sourceEntry.clock < source.clock := by
              simp [sourceEntry, DataSem.callEnv, pushEnv, decClock]
              omega
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
                    refine ⟨targetLast, ?_, lastRel⟩
                    simp [compile, savedLive, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped]
                  | raise value =>
                    have handlerRun : DataSem.evaluate handler (setVar name value last) = (result, sourceNext) := by
                      simpa [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped] using run
                    obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                      bodyIH body sourceEntry targetEntry last (some (.err (.raise value))) smaller entryRel.1 entryRel.2 entryException (by simp) called
                    obtain ⟨targetNext, targetHandlerRun, finalRel⟩ :=
                      handlerSimulation_afterRaise source target last targetLast sourceNext args size sourceEnv targetEnv body handler name value live result
                        handlerRel lastRel exception called targetRun handlerRun notType handlerIH
                    have targetClamped := targetRun
                    rw [← fixClock_evaluate body targetEntry] at targetClamped
                    simp only [targetEntry] at targetClamped
                    refine ⟨targetNext, ?_, finalRel⟩
                    simpa [compile, savedLive, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped] using targetHandlerRun
                | val returned =>
                  by_cases lengths : returned.length = returns.length
                  · obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                      bodyIH body sourceEntry targetEntry last (some (.val returned)) smaller entryRel.1 entryRel.2 entryException (by simp) called
                    have sourceControl := evaluate_stackResult body sourceEntry last (some (.val returned)) called
                    have targetControl := evaluate_stackResult body targetEntry targetLast (some (.val returned)) targetRun
                    obtain ⟨sourcePop, targetPop, sourcePopRun, targetPopRun, popRel⟩ :=
                      stateRel_popNonTail source target last targetLast args size sourceEnv targetEnv true (sptListDelete returns live)
                        lastRel returnRel sourceControl.1 sourceControl.2 targetControl.1 targetControl.2
                    simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped, lengths, sourcePopRun] at run
                    obtain ⟨rfl, rfl⟩ := run
                    have targetClamped : fixClock targetEntry (DataSem.evaluate body targetEntry) = (some (.val returned), targetLast) := by
                      rw [fixClock_evaluate, targetRun]
                    simp only [targetEntry] at targetClamped
                    refine ⟨setVars returns returned targetPop, ?_, stateRel_setVars sourcePop targetPop live returns returned lengths popRel⟩
                    simp [compile, savedLive, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped, lengths, targetPopRun]
                  · simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped, lengths] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact False.elim (notType rfl)
      · simp [DataSem.evaluate, read, found, unique] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)

/-- Every call form satisfies the liveness simulation assuming the handler
simulation and smaller-clock same-program evaluator simulation. -/
theorem call_correct_at {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (arguments : List Nat) (handler : Option (Nat × DataLang.Prog)) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate (.call ret dest arguments handler) source = (result, sourceNext))
    (related : stateRel source target (compile (.call ret dest arguments handler) live).2)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock)
    (handlerIH : ∀ name body, handler = some (name, body) → simulationFor (C := C) (F := F) body live) :
    ∃ targetNext, DataSem.evaluate (compile (.call ret dest arguments handler) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  cases ret with
  | none =>
    cases handler with
    | none => exact call_tail_correct dest arguments live source target sourceNext result run related exception notType bodyIH
    | some pair =>
      cases read : DataSem.getVars arguments source.locals with
      | none =>
        simp [DataSem.evaluate, read] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | some values =>
        cases found : findCode dest values source.code source.stackFrameSizes with
        | none =>
          simp [DataSem.evaluate, read, found] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
        | some triple =>
          obtain ⟨args, body, size⟩ := triple
          simp [DataSem.evaluate, read, found] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
  | some pair =>
    obtain ⟨returns, names⟩ := pair
    cases handler with
    | none => exact call_nonTail_noHandler_correct returns names dest arguments live source target sourceNext result run related exception notType bodyIH
    | some pair =>
      obtain ⟨name, body⟩ := pair
      exact call_nonTail_handler_correct returns names dest arguments name body live source target sourceNext result
        run related exception notType bodyIH (handlerIH name body rfl)

end Flapjack.Compiler.Backend.DataLive
