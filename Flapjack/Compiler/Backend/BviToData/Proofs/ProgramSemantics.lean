module

public import Flapjack.Compiler.Backend.BviToData.Proofs.ProgramEvaluate
public import Flapjack.Compiler.Backend.Semantics.BviSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics

@[expose] public section

/-! Whole-program behavioral correctness of BVI-to-data compilation. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Flapjack proof infrastructure: expose the fatal-run condition from the
source semantics when its behavior is not failure. -/
private theorem sourceNoFatal {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (start : Nat)
    (ok : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) :
    ¬∃ clock error,
      (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
  classical
  intro fatal
  apply ok
  simp [BviSem.semantics, fatal]

/-- Flapjack proof infrastructure: relate the two entry calls at one clock. -/
private theorem matchingClock {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (start : Nat) (limits : DataSem.Limits)
    (sizes : Spt Nat)
    (ok : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) (clock : Nat) :
    ∃ (r : Result (List DataSem.Value) DataSem.Value) (t : DataSem.State C F),
      DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState ffi (sptFromAList (compileProg program))
          (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
          compiler true limits sizes clock) = (some r, t) ∧
      dataToBviResult r = (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).1 ∧
      t.ffi = (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).2.ffi := by
  have noFatal := sourceNoFatal ffi program oracle compiler start ok
  generalize run : BviSem.evaluate [.call 0 (some start) [] none] []
    (BviSem.initialState ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) clock) = pair
  obtain ⟨res, s⟩ := pair
  have notType : res ≠ .err (.abort .typeError) := by
    intro eq
    apply noFatal
    refine ⟨clock, .abort .typeError, ?_, by simp, ?_⟩
    · simpa [BviSem.evaluateTuple, run] using eq
    · intro event; simp
  have notRaise : ∀ x, res ≠ .err (.raise x) := by
    intro x eq
    apply noFatal
    refine ⟨clock, .raise x, ?_, by simp, ?_⟩
    · simpa [BviSem.evaluateTuple, run] using eq
    · intro event; simp
  obtain ⟨r, t, target, rel, projected⟩ :=
    compileProgEvaluate ffi program oracle compiler clock start limits sizes res s run notType notRaise
  exact ⟨r, t, target, by simpa [BviSem.evaluateTuple, run] using projected,
    by simpa [BviSem.evaluateTuple, run] using rel.2.2.2.2.2.1.symm⟩

/-- Flapjack proof infrastructure: transfer non-failure to the target's
fatal-run condition. -/
private theorem targetNoFatal {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (start : Nat) (limits : DataSem.Limits)
    (sizes : Spt Nat)
    (ok : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) :
    ¬∃ clock, match (DataSem.evaluate (.call none (some start) [] none)
      (DataSem.initialState ffi (sptFromAList (compileProg program))
        (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
        compiler true limits sizes clock)).1 with
      | none => True
      | some (.err error) => error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
      | _ => False := by
  rintro ⟨clock, bad⟩
  obtain ⟨result, target, targetRun, projection, ffiEq⟩ :=
    matchingClock ffi program oracle compiler start limits sizes ok clock
  rw [targetRun] at bad
  cases result with
  | val values => simp at bad
  | err error =>
    have fatal := sourceNoFatal ffi program oracle compiler start ok
    apply fatal
    cases error with
    | abort reason =>
      refine ⟨clock, .abort reason, by simpa [dataToBviResult] using projection.symm, ?_, ?_⟩
      · simpa using bad.1
      · simpa using bad.2
    | raise value =>
      exact ⟨clock, .raise (.exn (dataToBviValue value)), by simpa [dataToBviResult] using projection.symm,
        by simp, by simp⟩

/-- Flapjack proof infrastructure: identify terminating observations using
the per-clock simulation. -/
private theorem matchingObservations {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (start : Nat) (limits : DataSem.Limits)
    (sizes : Spt Nat)
    (ok : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) :
    DataSem.terminatingObservation ffi (sptFromAList (compileProg program))
      (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
      compiler limits sizes start =
    BviSem.terminatingObservation ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start := by
  funext behavior
  apply propext
  constructor
  · rintro ⟨clock, target, result, outcome, run, ending, rfl⟩
    obtain ⟨r, t, actual, projection, ffiEq⟩ := matchingClock ffi program oracle compiler start limits sizes ok clock
    rw [run] at actual
    have same : r = result ∧ t = target := by simpa [eq_comm] using actual
    obtain ⟨sameR, sameT⟩ := same
    subst r
    subst t
    refine ⟨clock, dataToBviResult result,
      (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).2, outcome, ?_, ?_, ?_⟩
    · exact Prod.ext projection.symm rfl
    · cases result with
      | val values => simpa [dataToBviResult] using ending
      | err error =>
        cases error with
        | raise value => simp at ending
        | abort reason => cases reason <;> simp [dataToBviResult] at ending ⊢; assumption
    · simp [ffiEq]
  · rintro ⟨clock, result, state, outcome, run, ending, rfl⟩
    obtain ⟨r, t, actual, projection, ffiEq⟩ := matchingClock ffi program oracle compiler start limits sizes ok clock
    rw [run] at projection ffiEq
    refine ⟨clock, t, r, outcome, actual, ?_, ?_⟩
    · cases r with
      | val values => simp only [dataToBviResult] at projection; subst result; simpa using ending
      | err error =>
        cases error with
        | raise value => simp only [dataToBviResult] at projection; subst result; simp at ending
        | abort reason =>
          simp only [dataToBviResult] at projection
          subst result
          cases reason <;> simp_all
    · simp [ffiEq]

/-- If the source program does not fail, compiled DATA behavior equals its
complete BVI behavior, including termination and divergence. The semantics
inherit the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_prog_semantics"]
theorem compileProgSemantics {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (start : Nat) (limits : DataSem.Limits)
    (sizes : Spt Nat)
    (ok : BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start ≠ .fail) :
    DataSem.semantics ffi (sptFromAList (compileProg program))
      (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
      compiler limits sizes start =
    BviSem.semantics ffi (sptFromAList program) oracle
      (fun cfg code => compiler cfg (compileProg code)) start := by
  have noSource := sourceNoFatal ffi program oracle compiler start ok
  have noTarget := targetNoFatal ffi program oracle compiler start limits sizes ok
  have obs := matchingObservations ffi program oracle compiler start limits sizes ok
  have traces : ∀ clock,
      (DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState ffi (sptFromAList (compileProg program))
          (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
          compiler true limits sizes clock)).2.ffi.ioEvents =
      (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).2.ffi.ioEvents := by
    intro clock
    obtain ⟨result, state, run, projected, ffiEq⟩ :=
      matchingClock ffi program oracle compiler start limits sizes ok clock
    simpa [run] using congrArg HolFfiState.ioEvents ffiEq
  have traceSets : (fun trace => ∃ clock,
      trace = HolLList.fromList (DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState ffi (sptFromAList (compileProg program))
          (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
          compiler true limits sizes clock)).2.ffi.ioEvents) =
    (fun trace => ∃ clock,
      trace = HolLList.fromList (BviSem.evaluateTuple ([.call 0 (some start) [] none], [],
        BviSem.initialState ffi (sptFromAList program) oracle
          (fun cfg code => compiler cfg (compileProg code)) clock)).2.ffi.ioEvents) := by
    funext trace
    simp only [traces]
  simp only [DataSem.semantics, BviSem.semantics, if_neg noSource, obs, traceSets]
  split
  · rename_i bad
    exact False.elim (noTarget bad)
  · rfl

end Flapjack.Compiler.Backend.BviToData
