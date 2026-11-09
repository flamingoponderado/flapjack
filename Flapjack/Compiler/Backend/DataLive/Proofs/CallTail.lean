import Flapjack.Compiler.Backend.DataLive.Proofs.ForceTail
import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv

/-! Tail-call liveness simulation with the evaluator induction hypothesis. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A handler-free tail call simulates once same-program evaluation is
known at smaller clocks. The evaluator induction hypothesis remains an open
prerequisite, so this is not yet the complete HOL call case. -/
theorem call_tail_correct {C F : Type} (dest : Option Nat) (names : List Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate (.call none dest names none) source = (result, sourceNext))
    (related : stateRel source target (compile (.call none dest names none) live).2)
    (exception : exceptionRel source target)
    (notType : result ≠ some (.err (.abort .typeError)))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (compile (.call none dest names none) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  have initial : stateRel source target (BviToData.namesOfList names) := by simpa [compile] using related
  have readEq : DataSem.getVars names source.locals = DataSem.getVars names target.locals := by
    apply stateRel_getVars source target (BviToData.namesOfList names) names initial
    intro key member
    exact (BviToData.namesOfList_mem names key).2 member
  cases read : DataSem.getVars names source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some values =>
    have targetRead : DataSem.getVars names target.locals = some values := by rw [← readEq, read]
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
      by_cases zero : source.clock = 0
      · have targetZero : target.clock = 0 := by rw [← initial.2.1, zero]
        simp [DataSem.evaluate, read, found, zero] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨flushState true target, ?_, ?_⟩
        · simp [compile, DataSem.evaluate, targetRead, targetFound, targetZero]
        · simpa [installSfs, postLive] using stateRel_flushInstall source target _ (.intOp (.const 0)) initial
      · have targetNonzero : target.clock ≠ 0 := by rw [← initial.2.1]; exact zero
        let sourceEntry := DataSem.callEnv args size (decClock source)
        let targetEntry := DataSem.callEnv args size (decClock target)
        have entryRel := stateRel_tailEntry source target _ args size initial
        have entryException := exceptionRel_tailEntry source target _ args size initial exception
        have smaller : sourceEntry.clock < source.clock := by
          simp [sourceEntry, DataSem.callEnv, decClock]
          omega
        cases called : DataSem.evaluate body sourceEntry with
        | mk outcome last =>
          have calledUnfolded := called
          simp only [sourceEntry] at calledUnfolded
          cases outcome with
          | none =>
            simp [DataSem.evaluate, read, found, zero, calledUnfolded] at run
            obtain ⟨rfl, rfl⟩ := run
            exact False.elim (notType rfl)
          | some value =>
            simp [DataSem.evaluate, read, found, zero, calledUnfolded] at run
            obtain ⟨rfl, rfl⟩ := run
            obtain ⟨targetNext, targetRun, nextRel, _⟩ :=
              bodyIH body sourceEntry targetEntry last (some value) smaller entryRel.1 entryRel.2 entryException notType called
            refine ⟨targetNext, ?_, nextRel⟩
            simp only [targetEntry] at targetRun
            simp [compile, DataSem.evaluate, targetRead, targetFound, targetNonzero, targetRun]

/-- A tail call always stops rather than continuing in its caller. -/
theorem evaluate_tailCall_stops {C F : Type} (dest : Option Nat) (names : List Nat)
    (state : State C F) : (DataSem.evaluate (.call none dest names none) state).1 ≠ none := by
  simp only [DataSem.evaluate]
  repeat' (split <;> try simp_all)

/-- A tail force always stops rather than continuing in its caller. -/
theorem evaluate_tailForce_stops {C F : Type} (label src : Nat) (state : State C F) :
    (DataSem.evaluate (.force none label src) state).1 ≠ none := by
  simp only [DataSem.evaluate]
  repeat' (split <;> try simp_all)

/-- Same-program tail-call simulation at a fixed entry clock follows from
the smaller-clock evaluator induction hypothesis. -/
theorem evaluatorSimulation_tailCall_at {C F : Type} (dest : Option Nat) (names : List Nat)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.call none dest names none) source = (result, sourceNext))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.call none dest names none) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  have initial : stateRel source target (compile (.call none dest names none) .ln).2 :=
    stateRel_of_sameLocals source target _ related sameLocals
  obtain ⟨targetNext, targetRun, after⟩ := call_tail_correct dest names .ln source target sourceNext result run initial exception notType bodyIH
  have stopped : result ≠ none := by
    have stops := evaluate_tailCall_stops dest names source
    rw [run] at stops
    exact stops
  cases result with
  | none => exact False.elim (stopped rfl)
  | some value => exact ⟨targetNext, by simpa [compile] using targetRun, after, by simp⟩

/-- Same-program tail-force simulation at a fixed entry clock follows from
the smaller-clock evaluator induction hypothesis. -/
theorem evaluatorSimulation_tailForce_at {C F : Type} (label src : Nat)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.force none label src) source = (result, sourceNext))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.force none label src) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  have initial : stateRel source target (compile (.force none label src) .ln).2 :=
    stateRel_of_sameLocals source target _ related sameLocals
  obtain ⟨targetNext, targetRun, after⟩ := force_tail_correct label src .ln source target sourceNext result run initial exception notType bodyIH
  have stopped : result ≠ none := by
    have stops := evaluate_tailForce_stops label src source
    rw [run] at stops
    exact stops
  cases result with
  | none => exact False.elim (stopped rfl)
  | some value => exact ⟨targetNext, by simpa [compile] using targetRun, after, by simp⟩

/-- Tail calls with a handler are rejected with a type error, while
handler-free tail calls use the smaller-clock induction hypothesis. -/
theorem evaluatorSimulation_tailCall_anyHandler_at {C F : Type} (dest : Option Nat) (names : List Nat)
    (handler : Option (Nat × DataLang.Prog))
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.call none dest names handler) source = (result, sourceNext))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.call none dest names handler) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  cases handler with
  | none => exact evaluatorSimulation_tailCall_at dest names source target sourceNext result related sameLocals exception notType run bodyIH
  | some handler =>
    cases read : DataSem.getVars names source.locals with
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

end Flapjack.Compiler.Backend.DataLive
