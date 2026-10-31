import Flapjack.Compiler.Backend.BviTmc.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteSimulation

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

/-- Flapjack infrastructure: TMC compilation preserves whole-program BVI
behavior under the program and oracle conditions when the source does not
fail. The full HOL statement and its carriers remain to be source-reviewed. -/
theorem compileEach_semantics_assembled {C F : Type} (next start : Nat)
    (program : List (Nat × Nat × Bvi.Exp)) (ffi : HolFfiState F)
    (oracle : BviSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (condition : inputCondition next program)
    (oracleConditions : ∀ n, inputCondition (oracle n).1.1 (oracle n).2)
    (workerBound : ∀ n, n ∈ ((compileEachSource next program).2.map Prod.fst) →
      inWorkerNamespace n → n < (oracle 0).1.1)
    (notFail : BviSem.semantics ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) start =
      BviSem.semantics ffi (sptFromAList (compileEachSource next program).2)
        (stateCo compileEachSource oracle) compiler start := by
  apply semantics_eq_of_observations ffi _ _ oracle (stateCo compileEachSource oracle)
    (stateCc compileEachSource compiler) compiler start
  intro clock
  have noType := BviTailrec.semantics_ne_fail_no_type_error ffi (sptFromAList program) oracle
    (stateCc compileEachSource compiler) start notFail clock
  cases run : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) clock) with
  | mk result final =>
    have notType : result ≠ .err (.abort .typeError) := by simpa [run] using noType
    obtain ⟨f, targetFinal, targetResult, targetRun, related, states⟩ :=
      CompileSemantics.evaluate_compile_each_assembled next start clock program ffi oracle compiler result final
        condition oracleConditions workerBound run notType
    have observations := related_observations f result targetResult related
    have ffiEqual := states.2.2.2.1
    simp only [targetRun]
    exact ⟨observations.1, observations.2, (congrArg HolFfiState.ioEvents ffiEqual).symm⟩

/-- Flapjack infrastructure: the executed fuel-based TMC program traversal
preserves BVI behavior when enabled. The oracle still uses the source-shaped
pass, whose correspondence with the executable traversal is proved separately. -/
theorem compileProgFuel_enabled_semantics {C F : Type} (fuel next start : Nat)
    (program compiled : List (Nat × Nat × Bvi.Exp)) (last : Nat) (ffi : HolFfiState F)
    (oracle : BviSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (condition : inputCondition next program)
    (oracleConditions : ∀ n, inputCondition (oracle n).1.1 (oracle n).2)
    (workerBound : ∀ n, n ∈ (compiled.map Prod.fst) → inWorkerNamespace n → n < (oracle 0).1.1)
    (compiledEq : compileProgFuel fuel true next program = some (last, compiled))
    (notFail : BviSem.semantics ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) start =
      BviSem.semantics ffi (sptFromAList compiled) (stateCo compileEachSource oracle) compiler start := by
  have eq := (Option.some.inj ((compileProgFuel_eq_source fuel true next program).symm.trans compiledEq))
  have outputEq : (compileEachSource next program).2 = compiled := congrArg Prod.snd eq
  have bound : ∀ n, n ∈ ((compileEachSource next program).2.map Prod.fst) →
      inWorkerNamespace n → n < (oracle 0).1.1 := by
    rw [outputEq]
    exact workerBound
  simpa only [outputEq] using
    compileEach_semantics_assembled next start program ffi oracle compiler condition oracleConditions bound notFail

end Flapjack.Compiler.Backend.BviTmc.Observation
