module

public import Flapjack.Compiler.Backend.BviInline.Proofs.WholeProgramSimulation
public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateEventsClockFull
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteSimulation

@[expose] public section


/-! Whole-program observation support for the BVI inliner. -/
namespace Flapjack.Compiler.Backend.BviInline.Observation
open BviSem

namespace ClockEventCarrier
/-- The canonical BVI reference-map representation has a roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ClockEventCarrier

/-- Increasing an arbitrary initial clock extends the evaluation's I/O events.
The evaluator inherits the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_add_clock_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem evaluateAddClockIoEventsMono {C F : Type} (expressions : List Bvi.Exp)
    (env : List BvlSem.Value) (state : BviState C F) (clock extra : Nat) :
    (evaluateTuple (expressions, env, { state with clock := clock })).2.ffi.ioEvents <+:
      (evaluateTuple (expressions, env, { state with clock := clock + extra })).2.ffi.ioEvents := by
  simpa [evaluateTuple] using
    BviProps.evaluate_addClock_ioEvents_prefix expressions env { state with clock := clock } extra

/-- Flapjack infrastructure: if each target trace is a source trace at an
equal or later clock, and both families grow by prefix as clocks increase,
their divergent least-upper-bound traces are equal. -/
theorem cofinal_trace_lub {α : Type} (source target : Nat → List α)
    (sourceMono : ∀ clock extra, source clock <+: source (clock + extra))
    (targetMono : ∀ clock extra, target clock <+: target (clock + extra))
    (cofinal : ∀ clock, ∃ extra, target clock = source (clock + extra)) :
    HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (source clock)) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (target clock)) := by
  let sourceSet : HolLList α → Prop := fun trace => ∃ clock, trace = HolLList.fromList (source clock)
  let targetSet : HolLList α → Prop := fun trace => ∃ clock, trace = HolLList.fromList (target clock)
  have sourceChain : HolLList.lprefixChain sourceSet := by
    rintro first second ⟨i, hi⟩ ⟨j, hj⟩
    subst first
    subst second
    rcases Nat.le_total i j with earlier | later
    · left
      apply (HolLList.lprefix_fromList _ _).2
      simpa [Nat.add_sub_of_le earlier] using sourceMono i (j - i)
    · right
      apply (HolLList.lprefix_fromList _ _).2
      simpa [Nat.add_sub_of_le later] using sourceMono j (i - j)
  have targetChain : HolLList.lprefixChain targetSet := by
    rintro first second ⟨i, hi⟩ ⟨j, hj⟩
    subst first
    subst second
    rcases Nat.le_total i j with earlier | later
    · left
      apply (HolLList.lprefix_fromList _ _).2
      simpa [Nat.add_sub_of_le earlier] using targetMono i (j - i)
    · right
      apply (HolLList.lprefix_fromList _ _).2
      simpa [Nat.add_sub_of_le later] using targetMono j (i - j)
  have forward : HolLList.lprefixRel sourceSet targetSet := by
    rintro trace ⟨clock, equalTrace⟩
    subst trace
    obtain ⟨extra, equal⟩ := cofinal clock
    refine ⟨HolLList.fromList (target clock), ⟨clock, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).2
    rw [equal]
    exact sourceMono clock extra
  have backward : HolLList.lprefixRel targetSet sourceSet := by
    rintro trace ⟨clock, equalTrace⟩
    subst trace
    obtain ⟨extra, equal⟩ := cofinal clock
    refine ⟨HolLList.fromList (source (clock + extra)), ⟨clock + extra, rfl⟩, ?_⟩
    rw [equal]
    exact HolLList.lprefix_refl _
  exact HolLList.IMP_build_lprefix_lub_EQ sourceChain targetChain forward backward

/-- Flapjack infrastructure: cofinal initial executions determine the same
observable BVI behavior when the source does not fail. -/
theorem semantics_eq_of_cofinal {C D F : Type} (ffi : HolFfiState F)
    (sourceCode targetCode : Spt (Nat × Bvi.Exp)) (sourceOracle : BviSem.CompileOracle C)
    (targetOracle : BviSem.CompileOracle D) (sourceCompiler : BviSem.Compiler C)
    (targetCompiler : BviSem.Compiler D) (start : Nat)
    (notFail : BviSem.semantics ffi sourceCode sourceOracle sourceCompiler start ≠ .fail)
    (cofinal : ∀ clock, ∃ extra,
      let source := evaluate [.call 0 (some start) [] none] []
        (initialState ffi sourceCode sourceOracle sourceCompiler (clock + extra))
      let target := evaluate [.call 0 (some start) [] none] []
        (initialState ffi targetCode targetOracle targetCompiler clock)
      source.1 = target.1 ∧ source.2.ffi = target.2.ffi) :
    BviSem.semantics ffi targetCode targetOracle targetCompiler start =
      BviSem.semantics ffi sourceCode sourceOracle sourceCompiler start := by
  classical
  let src := fun clock => evaluate [.call 0 (some start) [] none] []
    (initialState ffi sourceCode sourceOracle sourceCompiler clock)
  let tgt := fun clock => evaluate [.call 0 (some start) [] none] []
    (initialState ffi targetCode targetOracle targetCompiler clock)
  have sourceNoFatal : ¬ ∃ clock error, (src clock).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
    intro fatal
    apply notFail
    have fatal' : ∃ clock error, (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi sourceCode sourceOracle sourceCompiler clock)).1 = .err error ∧
        error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := fatal
    simp [BviSem.semantics, fatal']
  have targetNoFatal : ¬ ∃ clock error, (tgt clock).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
    rintro ⟨clock, error, resultEq, notTimeout, notFfi⟩
    obtain ⟨extra, equalResult, _⟩ := cofinal clock
    apply sourceNoFatal
    exact ⟨clock + extra, error, equalResult.trans resultEq, notTimeout, notFfi⟩
  have observations : terminatingObservation ffi sourceCode sourceOracle sourceCompiler start =
      terminatingObservation ffi targetCode targetOracle targetCompiler start := by
    funext behavior
    apply propext
    rw [BviTailrec.terminatingObservation_iff_projections, BviTailrec.terminatingObservation_iff_projections]
    constructor
    · rintro ⟨clock, outcome, outcomeRun, behaviorEq⟩
      cases targetRun : tgt clock with
      | mk targetResult targetState =>
        obtain ⟨extra, resultEq, ffiEq⟩ := cofinal clock
        have sourceNotTimeout : (src clock).1 ≠ .err (.abort .timeoutError) := by
          intro eq
          rw [eq] at outcomeRun
          simp at outcomeRun
        cases sourceRun : src clock with
        | mk sourceResult sourceState =>
          have notTimeout : sourceResult ≠ .err (.abort .timeoutError) := by simpa [sourceRun] using sourceNotTimeout
          have shifted := BviProps.evaluate_addClock [.call 0 (some start) [] none] []
            (initialState ffi sourceCode sourceOracle sourceCompiler clock) sourceState sourceResult extra
              sourceRun notTimeout
          have sourceShift : src (clock + extra) = (sourceResult, { sourceState with clock := sourceState.clock + extra }) := by
            simpa [src, initialState] using shifted
          change (src (clock + extra)).1 = (tgt clock).1 at resultEq
          change (src (clock + extra)).2.ffi = (tgt clock).2.ffi at ffiEq
          rw [sourceShift, targetRun] at resultEq ffiEq
          have sameResult : sourceResult = targetResult := resultEq
          have sameEvents : sourceState.ffi.ioEvents = targetState.ffi.ioEvents := congrArg HolFfiState.ioEvents ffiEq
          refine ⟨clock, outcome, ?_, ?_⟩
          · change (match (tgt clock).1 with
              | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
              | .val _ => outcome = HolOutcome.success
              | _ => False)
            rw [targetRun, ← sameResult]
            cases sourceResult with
            | val values => simpa [src, sourceRun] using outcomeRun
            | err error => cases error with
              | raise payload => simp [src, sourceRun] at outcomeRun
              | abort reason =>
                cases reason with
                | typeError => simp [src, sourceRun] at outcomeRun
                | timeoutError => simp [src, sourceRun] at outcomeRun
                | ffiError event => simpa [src, sourceRun] using outcomeRun
          · change behavior = HolBehaviour.terminate outcome (tgt clock).2.ffi.ioEvents
            rw [targetRun, ← sameEvents]
            simpa [src, sourceRun] using behaviorEq
    · rintro ⟨clock, outcome, outcomeRun, behaviorEq⟩
      obtain ⟨extra, resultEq, ffiEq⟩ := cofinal clock
      refine ⟨clock + extra, outcome, ?_, ?_⟩
      · change (match (src (clock + extra)).1 with
          | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
          | .val _ => outcome = HolOutcome.success
          | _ => False)
        rw [resultEq]
        exact outcomeRun
      · change behavior = HolBehaviour.terminate outcome (src (clock + extra)).2.ffi.ioEvents
        rw [ffiEq]
        exact behaviorEq
  have traces : HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (src clock).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (tgt clock).2.ffi.ioEvents) := by
    apply cofinal_trace_lub (fun clock => (src clock).2.ffi.ioEvents) (fun clock => (tgt clock).2.ffi.ioEvents)
    · intro clock extra
      simpa [src, initialState, evaluateTuple] using evaluateAddClockIoEventsMono
        [.call 0 (some start) [] none] [] (initialState ffi sourceCode sourceOracle sourceCompiler clock) clock extra
    · intro clock extra
      simpa [tgt, initialState, evaluateTuple] using evaluateAddClockIoEventsMono
        [.call 0 (some start) [] none] [] (initialState ffi targetCode targetOracle targetCompiler clock) clock extra
    · intro clock
      obtain ⟨extra, _, ffiEq⟩ := cofinal clock
      exact ⟨extra, congrArg HolFfiState.ioEvents ffiEq.symm⟩
  unfold BviSem.semantics
  dsimp only
  dsimp only [src, tgt] at sourceNoFatal targetNoFatal traces
  simp [BviSem.evaluateTuple, targetNoFatal, sourceNoFatal, ← observations, ← traces]

/-- Whole-program BVI inlining preserves the source behavior. The semantics
inherit the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "compile_prog_semantics"]
theorem compileProgSource_semantics {C F : Type}
    (program : List (Nat × Nat × Bvi.Exp)) (cache : Spt (Nat × Bvi.Exp))
    (output : List (Nat × Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C)) (ffi : HolFfiState F)
    (compiler : BviSem.Compiler C) (start : Nat)
    (premises : compileProgSource program = (cache, output) ∧
      (oracle 0).1.1 = cache ∧ (program.map Prod.fst).Nodup)
    (notFail : BviSem.semantics ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList output) (BackendProps.stateCo compileIncSource oracle) compiler start =
      BviSem.semantics ffi (sptFromAList program) oracle (BackendProps.stateCc compileIncSource compiler) start := by
  obtain ⟨sourceRun, oracleCache, distinct⟩ := premises
  apply semantics_eq_of_cofinal ffi (sptFromAList program) (sptFromAList output) oracle
    (BackendProps.stateCo compileIncSource oracle) (BackendProps.stateCc compileIncSource compiler) compiler start notFail
  intro clock
  cases targetRun : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList output) (BackendProps.stateCo compileIncSource oracle) compiler clock) with
  | mk result targetNext =>
    have safe := BviInline.Proofs.semanticsNoTypeError ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource compiler) start notFail
    obtain ⟨extra, sourceNext, sourceRun, ffiEq⟩ :=
      evaluateCompileProg program cache output oracle ffi compiler clock start result targetNext
        ⟨sourceRun, oracleCache, distinct, safe, targetRun⟩
    simp only [evaluateTuple] at sourceRun
    refine ⟨extra, ?_, ?_⟩
    · rw [sourceRun]
    · rw [sourceRun]
      exact ffiEq

end Flapjack.Compiler.Backend.BviInline.Observation
