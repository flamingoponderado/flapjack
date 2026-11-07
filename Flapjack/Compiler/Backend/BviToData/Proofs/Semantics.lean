import Flapjack.Compiler.Backend.BviToData.Proofs.Program
import Flapjack.Compiler.Backend.Semantics.BviSem.Semantics
import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics

/-! Observable BVI-to-data compiler behavior. These Lean-side results remain
untagged pending source evaluator and carrier correspondence review. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- When the source's whole-program semantics is not failure, every finite
clock gives matching target and source initial-call results and FFI states. -/
theorem initialRuns_match {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat) (start : Nat)
    (noFail : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) :
    ∀ clock, ∃ result last,
      DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState ffi (sptFromAList (compileProg program))
          (fun n => let (cfg, code) := oracle n; (cfg, compileProg code)) compiler true limits sizes clock) =
        (some result, last) ∧
      dataToBviResult result = (BviSem.evaluate [.call 0 (some start) [] none] []
        (BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).1 ∧
      last.ffi = (BviSem.evaluate [.call 0 (some start) [] none] []
        (BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).2.ffi := by
  classical
  have noFatal : ¬ ∃ clock error,
      (BviSem.evaluate [.call 0 (some start) [] none] []
        (BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
    intro fatal
    apply noFail
    simp [BviSem.semantics, BviSem.evaluateTuple, fatal]
  intro clock
  generalize run : BviSem.evaluate [.call 0 (some start) [] none] []
    (BviSem.initialState ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) clock) = pair
  obtain ⟨res, sourceLast⟩ := pair
  have notType : res ≠ .err (.abort .typeError) := by
    intro eq
    apply noFatal
    refine ⟨clock, .abort .typeError, ?_, by simp, by simp⟩
    simpa [run] using eq
  have notRaise : ∀ x, res ≠ .err (.raise x) := by
    intro x eq
    apply noFatal
    refine ⟨clock, .raise x, ?_, by simp, by simp⟩
    simpa [run] using eq
  obtain ⟨result, last, targetRun, related, projection⟩ :=
    compileProg_evaluate ffi program oracle compiler true limits sizes clock start res sourceLast run notType notRaise
  exact ⟨result, last, targetRun, by simpa [run] using projection, by simpa [run] using related.2.2.2.2.2.1.symm⟩

private theorem outcome_projection (r : Result (List DataSem.Value) DataSem.Value) (outcome : HolOutcome) :
    (match r, outcome with
     | .err (.abort (.ffiError event)), o => o = HolOutcome.ffiOutcome event
     | .val _, o => o = HolOutcome.success
     | _, _ => False) ↔
    (match dataToBviResult r, outcome with
     | .err (.abort (.ffiError event)), o => o = HolOutcome.ffiOutcome event
     | .val _, o => o = HolOutcome.success
     | _, _ => False) := by
  cases r with
  | val values => rfl
  | err error => cases error with
    | raise value => rfl
    | abort reason => cases reason <;> rfl

/-- The current Lean BVI and data observational semantics agree for a
non-failing source program. This is untagged pending review against the HOL
semantics and its carriers. -/
theorem compileProg_semantics {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat) (start : Nat)
    (noFail : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) :
    DataSem.semantics ffi (sptFromAList (compileProg program))
      (fun n => let (cfg, code) := oracle n; (cfg, compileProg code)) compiler limits sizes start =
    BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start := by
  classical
  let sourceCode := sptFromAList program
  let targetCode := sptFromAList (compileProg program)
  let sourceCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (compileProg code)
  let targetOracle : DataSem.CompileOracle C := fun n => let (cfg, code) := oracle n; (cfg, compileProg code)
  let sourceRun := fun clock => BviSem.evaluate [.call 0 (some start) [] none] []
    (BviSem.initialState ffi sourceCode oracle sourceCompiler clock)
  let targetRun := fun clock => DataSem.evaluate (.call none (some start) [] none)
    (DataSem.initialState ffi targetCode targetOracle compiler true limits sizes clock)
  have sourceNoFatal : ¬ ∃ clock error, (sourceRun clock).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
    intro fatal
    apply noFail
    have fatal' : ∃ clock error, (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).1 = .err error ∧
        error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
      simpa [sourceRun, sourceCode, sourceCompiler, BviSem.evaluateTuple] using fatal
    simp [BviSem.semantics, fatal']
  have paired : ∀ clock, ∃ result last, targetRun clock = (some result, last) ∧
      dataToBviResult result = (sourceRun clock).1 ∧ last.ffi = (sourceRun clock).2.ffi := by
    intro clock
    simpa [sourceRun, targetRun, sourceCode, targetCode, sourceCompiler, targetOracle] using
      initialRuns_match ffi program oracle compiler limits sizes start noFail clock
  have targetNoFatal : ¬ ∃ clock, match (targetRun clock).1 with
      | none => True
      | some (.err error) => error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
      | _ => False := by
    rintro ⟨clock, fatal⟩
    obtain ⟨result, last, run, projected, ffiEq⟩ := paired clock
    rw [run] at fatal
    cases result with
    | val values => simp at fatal
    | err error =>
      simp only at fatal
      cases error with
      | abort reason =>
        apply sourceNoFatal
        exact ⟨clock, .abort reason, by simpa [dataToBviResult] using projected.symm,
          by simpa using fatal.1, by simpa using fatal.2⟩
      | raise value =>
        apply sourceNoFatal
        refine ⟨clock, .raise (.exn (dataToBviValue value)), ?_, by simp, by simp⟩
        simpa [dataToBviResult] using projected.symm
  have observations : DataSem.terminatingObservation ffi targetCode targetOracle compiler limits sizes start =
      BviSem.terminatingObservation ffi sourceCode oracle sourceCompiler start := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, targetLast, result, outcome, run, resultOutcome, rfl⟩
      obtain ⟨otherResult, otherLast, targetPair, projected, ffiEq⟩ := paired clock
      have same : (some otherResult, otherLast) = (some result, targetLast) := targetPair.symm.trans run
      cases same
      refine ⟨clock, (sourceRun clock).1, (sourceRun clock).2, outcome, ?_, ?_, ?_⟩
      · exact Prod.eta _
      · rw [← projected]
        exact (outcome_projection result outcome).mp resultOutcome
      · simp [ffiEq]
    · rintro ⟨clock, result, sourceLast, outcome, run, resultOutcome, rfl⟩
      obtain ⟨targetResult, targetLast, targetPair, projected, ffiEq⟩ := paired clock
      have sourcePair : sourceRun clock = (result, sourceLast) := run
      rw [sourcePair] at projected ffiEq
      refine ⟨clock, targetLast, targetResult, outcome, targetPair, ?_, ?_⟩
      · apply (outcome_projection targetResult outcome).mpr
        rw [projected]
        cases result with
        | val values => exact resultOutcome
        | err error => cases error with
          | raise value => exact resultOutcome
          | abort reason => cases reason <;> exact resultOutcome
      · simp [ffiEq]
  have traces : (fun trace => ∃ clock, trace = HolLList.fromList (targetRun clock).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList (sourceRun clock).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, eq⟩
    · obtain ⟨result, last, run, _, ffiEq⟩ := paired clock
      refine ⟨clock, ?_⟩
      simpa [run, ffiEq] using eq
    · obtain ⟨result, last, run, _, ffiEq⟩ := paired clock
      refine ⟨clock, ?_⟩
      simpa [run, ffiEq] using eq
  change DataSem.semantics ffi targetCode targetOracle compiler limits sizes start =
    BviSem.semantics ffi sourceCode oracle sourceCompiler start
  unfold DataSem.semantics BviSem.semantics
  change (if (∃ clock, match (targetRun clock).1 with
      | none => True
      | some (.err error) => error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
      | _ => False) then HolBehaviour.fail else _) =
    (if (∃ clock error, (sourceRun clock).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) then HolBehaviour.fail else _)
  simp only [targetNoFatal, sourceNoFatal, ite_false]
  rw [observations, traces]
  rfl

end Flapjack.Compiler.Backend.BviToData
