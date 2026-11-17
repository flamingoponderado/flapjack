module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.CompileSemantics
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteSimulation

@[expose] public section


/-! Whole-program observations for the TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.Observation
open BviTmc BviSem BvlSem BackendProps SemanticPrimitivesProps ResultRelation

/-- Flapjack observation helper: errors that cause BVI semantics to fail. -/
def fatalResult : BviResult → Prop
  | .err error => error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
  | .val _ => False

/-- Flapjack observation helper: the termination outcome of a BVI result. -/
def resultOutcome (result : BviResult) (outcome : HolOutcome) : Prop :=
  match result with
  | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | .val _ => outcome = .success
  | _ => False

/-- Flapjack infrastructure: related results have the same fatal and
termination observations even when their values contain renamed pointers. -/
theorem related_observations (f : HolFiniteMapExact Nat Nat) (source target : BviResult)
    (related : resultRel (List.Forall₂ (valueRel f)) (eorRel f) source target) :
    (fatalResult source ↔ fatalResult target) ∧
      ∀ outcome, resultOutcome source outcome ↔ resultOutcome target outcome := by
  cases source with
  | val values =>
    cases target with
    | val values' => simp [fatalResult, resultOutcome]
    | err error => simp [resultRel] at related
  | err error =>
    cases target with
    | val values => simp [resultRel] at related
    | err error' =>
      cases error with
      | abort reason =>
        cases error' with
        | abort reason' =>
          have same : reason = reason' := by simpa [resultRel, excRel] using related
          subst reason'
          exact ⟨Iff.rfl, fun _ => Iff.rfl⟩
        | raise payload => simp [resultRel, excRel] at related
      | raise payload =>
        cases error' with
        | abort reason => simp [resultRel, excRel] at related
        | raise payload' => simp [fatalResult, resultOutcome]

/-- Flapjack infrastructure: the fatal-result predicate in the form used by
the BVI whole-program semantics. -/
theorem fatalResult_iff (result : BviResult) :
    fatalResult result ↔ ∃ error, result = .err error ∧ error ≠ .abort .timeoutError ∧
      ∀ event, error ≠ .abort (.ffiError event) := by
  cases result <;> simp [fatalResult]

/-- Flapjack infrastructure: pointwise agreement of fatal status, termination
outcomes, and traces determines equal whole-program BVI semantics. -/
theorem semantics_eq_of_observations {C D F : Type} (ffi : HolFfiState F)
    (code1 code2 : Spt (Nat × Bvi.Exp)) (oracle1 : BviSem.CompileOracle C)
    (oracle2 : BviSem.CompileOracle D) (compiler1 : BviSem.Compiler C)
    (compiler2 : BviSem.Compiler D) (start : Nat)
    (same : ∀ clock,
      let first := evaluate [.call 0 (some start) [] none] [] (initialState ffi code1 oracle1 compiler1 clock)
      let second := evaluate [.call 0 (some start) [] none] [] (initialState ffi code2 oracle2 compiler2 clock)
      (fatalResult first.1 ↔ fatalResult second.1) ∧
      (∀ outcome, resultOutcome first.1 outcome ↔ resultOutcome second.1 outcome) ∧
      first.2.ffi.ioEvents = second.2.ffi.ioEvents) :
    BviSem.semantics ffi code1 oracle1 compiler1 start = BviSem.semantics ffi code2 oracle2 compiler2 start := by
  classical
  have fatalEq : (∃ clock error, (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code1 oracle1 compiler1 clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) ↔
      (∃ clock error, (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code2 oracle2 compiler2 clock)).1 = .err error ∧
        error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) := by
    simp only [← fatalResult_iff]
    exact exists_congr (fun clock => (same clock).1)
  have observationEq : BviSem.terminatingObservation ffi code1 oracle1 compiler1 start =
      BviSem.terminatingObservation ffi code2 oracle2 compiler2 start := by
    funext behavior
    apply propext
    rw [BviTailrec.terminatingObservation_iff_projections, BviTailrec.terminatingObservation_iff_projections]
    constructor
    · rintro ⟨clock, outcome, result, trace⟩
      exact ⟨clock, outcome, ((same clock).2.1 outcome).mp result,
        by rw [← (same clock).2.2]; exact trace⟩
    · rintro ⟨clock, outcome, result, trace⟩
      exact ⟨clock, outcome, ((same clock).2.1 outcome).mpr result,
        by rw [(same clock).2.2]; exact trace⟩
  have traceEq : (fun trace => ∃ clock, trace = HolLList.fromList
      (evaluateTuple ([.call 0 (some start) [] none], [], initialState ffi code1 oracle1 compiler1 clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluateTuple ([.call 0 (some start) [] none], [], initialState ffi code2 oracle2 compiler2 clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    exact exists_congr (fun clock => by
      change trace = HolLList.fromList (evaluate [.call 0 (some start) [] none] []
        (initialState ffi code1 oracle1 compiler1 clock)).2.ffi.ioEvents ↔ _
      rw [(same clock).2.2]
      rfl)
  unfold BviSem.semantics
  dsimp only
  rw [propext fatalEq, observationEq, traceEq]

/-- TMC compilation preserves whole-program BVI behavior under the original
program and oracle conditions. The semantics inherit the rational-cuts real
model documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_semantics"]
theorem compileEach_semantics {C F : Type} (next start : Nat)
    (program : List (Nat × Nat × Bvi.Exp)) (ffi : HolFfiState F)
    (oracle : BviSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (compiled : List (Nat × Nat × Bvi.Exp))
    (h : inputCondition next program ∧
      (∀ k n cfg prog, oracle k = ((n, cfg), prog) → inputCondition n prog) ∧
      (∀ n, n ∈ compiled.map Prod.fst ∧ inWorkerNamespace n → n < (oracle 0).1.1) ∧
      (compileEachSource next program).2 = compiled ∧
      BviSem.semantics ffi (sptFromAList program) oracle
        (stateCc compileEachSource compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) start =
      BviSem.semantics ffi (sptFromAList compiled)
        (stateCo compileEachSource oracle) compiler start := by
  obtain ⟨condition, oracleCondition, workerCondition, outputEq, notFail⟩ := h
  subst compiled
  have oracleConditions : ∀ n, inputCondition (oracle n).1.1 (oracle n).2 :=
    fun n => oracleCondition n _ _ _ rfl
  have workerBound : ∀ n, n ∈ ((compileEachSource next program).2.map Prod.fst) →
      inWorkerNamespace n → n < (oracle 0).1.1 :=
    fun n member worker => workerCondition n ⟨member, worker⟩
  apply semantics_eq_of_observations ffi _ _ oracle (stateCo compileEachSource oracle)
    (stateCc compileEachSource compiler) compiler start
  intro clock
  have noType := BviInline.Proofs.semanticsNoTypeError ffi (sptFromAList program) oracle
    (stateCc compileEachSource compiler) start notFail clock
  cases run : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) clock) with
  | mk result final =>
    have notType : result ≠ .err (.abort .typeError) := by simpa [BviSem.evaluateTuple, run] using noType
    obtain ⟨f, targetFinal, targetResult, targetRun, related, states⟩ :=
      CompileSemantics.evaluate_compile_each_assembled next start clock program ffi oracle compiler result final
        ⟨condition, (fun n next cfg prog eq => by
          have h := oracleConditions n
          simpa [eq] using h), (fun n h => workerBound n h.1 h.2), run, notType⟩
    have observations := related_observations f result targetResult related
    have ffiEqual := (stateRel_const f final targetFinal states).2
    simp only [targetRun]
    exact ⟨observations.1, observations.2, (congrArg HolFfiState.ioEvents ffiEqual).symm⟩

/-- Whole-program TMC preserves BVI behavior under the original oracle and
worker conditions. The semantics inherit the real-model assumption documented
in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_prog_semantics"]
theorem compileProgSource_semantics {C F : Type} (next : Nat)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle (Nat × C))
    (compiled : List (Nat × Nat × Bvi.Exp)) (enabled : Bool) (ffi : HolFfiState F)
    (compiler : BviSem.Compiler C) (start : Nat)
    (premises : inputCondition next program ∧
      (∀ k n cfg prog, oracle k = ((n, cfg), prog) → inputCondition n prog) ∧
      (∀ n, n ∈ compiled.map Prod.fst ∧ inWorkerNamespace n → n < (oracle 0).1.1) ∧
      (compileProgSource enabled next program).2 = compiled ∧
      BviSem.semantics ffi (sptFromAList program) oracle
        (stateCc (compileProgSource enabled) compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList program) oracle
        (stateCc (compileProgSource enabled) compiler) start =
      BviSem.semantics ffi (sptFromAList compiled)
        (stateCo (compileProgSource enabled) oracle) compiler start := by
  obtain ⟨condition, oracleCondition, workerBound, compiledEq, notFail⟩ := premises
  cases enabled with
  | false =>
    have passEq : compileProgSource false = (fun c p => (c, p)) := by funext c p; rfl
    rw [passEq] at notFail ⊢
    have same : program = compiled := by simpa [compileProgSource] using compiledEq
    subst compiled
    exact BviTailrec.semantics_identity_adapter ffi (sptFromAList program) oracle compiler start notFail
  | true =>
    have passEq : compileProgSource true = compileEachSource := by funext c p; rfl
    rw [passEq] at notFail ⊢
    have outputEq : (compileEachSource next program).2 = compiled := by
      simpa [compileProgSource] using compiledEq
    exact compileEach_semantics next start program ffi oracle compiler compiled
      ⟨condition, oracleCondition, workerBound, outputEq, notFail⟩

end Flapjack.Compiler.Backend.BviTmc.Observation
