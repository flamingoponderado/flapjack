module

public import Flapjack.Compiler.Backend.DataLive.Proofs.ForceCall

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Handler-free non-tail call simulation for data liveness. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- With equally long name and value lists, every name has a binding in the
environment constructed for a call return. -/
theorem returnBindings_present (names : List Nat) (values : List DataSem.Value)
    (lengths : values.length = names.length) (key : Nat) (member : key ∈ names) :
    (sptLookup key (sptFromAList (names.zip values))).isSome := by
  induction names generalizing values with
  | nil => simp at member
  | cons name names ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      by_cases eq : key = name
      · subst key
        simp [sptFromAList, sptLookup_sptInsert_same]
      · have rest : key ∈ names := by simpa [eq] using member
        simpa [sptFromAList, sptLookup_sptInsert_ne name key value _ eq] using ih values lengths rest

/-- Writing a full return tuple restores agreement on every live local. -/
theorem stateRel_setVars {C F : Type} (source target : State C F) (live : NumSet)
    (names : List Nat) (values : List DataSem.Value) (lengths : values.length = names.length)
    (related : stateRel source target (sptListDelete names live)) :
    stateRel (setVars names values source) (setVars names values target) live := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  simp only [setVars, sptLookup_sptUnion]
  by_cases nameMember : key ∈ names
  · have present := returnBindings_present names values lengths key nameMember
    cases found : sptLookup key (sptFromAList (names.zip values)) <;> simp_all
  · have active : sptMem key (sptListDelete names live) := by
      simpa [sptMem, sptDomain, sptLookup_sptListDelete, nameMember] using member
    rw [locals key active]

/-- A non-tail call without a handler is simulated assuming the same-program
evaluator simulation at smaller clocks. The latter remains an open premise. -/
theorem call_nonTail_noHandler_correct {C F : Type} (returns : List Nat) (names : NumSet)
    (dest : Option Nat) (arguments : List Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate (.call (some (returns, names)) dest arguments none) source = (result, sourceNext))
    (related : stateRel source target (compile (.call (some (returns, names)) dest arguments none) live).2)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (compile (.call (some (returns, names)) dest arguments none) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  have initial : stateRel source target (sptListInsert arguments (sptInter names (sptListDelete returns live))) := by
    simpa [compile] using related
  have readEq := stateRel_getVars_listInsert source target arguments (sptInter names (sptListDelete returns live)) initial
  have cutRel : stateRel source target (sptInter names (sptListDelete returns live)) :=
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
          obtain ⟨targetEnv, targetCut, savedLocals⟩ := cutEnv_inter_related source target names (sptListDelete returns live) cutRel sourceEnv cut
          have savedRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv } (sptListDelete returns live) := by
            rcases initial with ⟨code, clock, space, ffi, refEq, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
            exact ⟨code, clock, space, ffi, refEq, global, handler, stack, compiler, oracle, stamps, limits, frames, savedLocals⟩
          by_cases zero : source.clock = 0
          · have targetZero : target.clock = 0 := by rw [← initial.2.1, zero]
            simp [DataSem.evaluate, read, found, unique, cut, zero] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨{ (DataSem.callEnv args size (pushEnv targetEnv false (decClock target))) with stack := [], locals := .ln }, ?_, ?_⟩
            · simp [compile, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetZero]
            · simpa [zero, postLive, DataSem.callEnv, pushEnv, decClock] using
                stateRel_forceTimeoutCall source target _ args size sourceEnv targetEnv initial
          · have targetNonzero : target.clock ≠ 0 := by rw [← initial.2.1]; exact zero
            let sourceEntry := DataSem.callEnv args size (pushEnv sourceEnv false (decClock source))
            let targetEntry := DataSem.callEnv args size (pushEnv targetEnv false (decClock target))
            have entryRel := stateRel_nonTailEntry source target _ args size sourceEnv targetEnv false initial
            have entryException := exceptionRel_nonTailEntry_noHandler source target _ args size sourceEnv targetEnv initial exception
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
                  cases error <;>
                    simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped] at run
                  all_goals
                    obtain ⟨rfl, rfl⟩ := run
                    obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                      bodyIH body sourceEntry targetEntry last _ smaller entryRel.1 entryRel.2 entryException notType called
                    have targetClamped := targetRun
                    rw [← fixClock_evaluate body targetEntry] at targetClamped
                    simp only [targetEntry] at targetClamped
                    refine ⟨targetLast, ?_, lastRel⟩
                    simp [compile, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped]
                | val returned =>
                  by_cases lengths : returned.length = returns.length
                  · obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                      bodyIH body sourceEntry targetEntry last (some (.val returned)) smaller entryRel.1 entryRel.2 entryException (by simp) called
                    have sourceControl := evaluate_stackResult body sourceEntry last (some (.val returned)) called
                    have targetControl := evaluate_stackResult body targetEntry targetLast (some (.val returned)) targetRun
                    obtain ⟨sourcePop, targetPop, sourcePopRun, targetPopRun, popRel⟩ :=
                      stateRel_popNonTail source target last targetLast args size sourceEnv targetEnv false (sptListDelete returns live)
                        lastRel savedRel sourceControl.1 sourceControl.2 targetControl.1 targetControl.2
                    simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped, lengths, sourcePopRun] at run
                    obtain ⟨rfl, rfl⟩ := run
                    have targetClamped : fixClock targetEntry (DataSem.evaluate body targetEntry) = (some (.val returned), targetLast) := by
                      rw [fixClock_evaluate, targetRun]
                    simp only [targetEntry] at targetClamped
                    refine ⟨setVars returns returned targetPop, ?_, stateRel_setVars sourcePop targetPop live returns returned lengths popRel⟩
                    simp [compile, DataSem.evaluate, targetRead, targetFound, unique, targetCut, targetNonzero, targetClamped, lengths, targetPopRun]
                  · simp [DataSem.evaluate, read, found, unique, cut, zero, sourceClamped, lengths] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact False.elim (notType rfl)
      · simp [DataSem.evaluate, read, found, unique] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)

end Flapjack.Compiler.Backend.DataLive
