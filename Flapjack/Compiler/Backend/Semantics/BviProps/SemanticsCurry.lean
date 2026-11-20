module

public import Flapjack.Compiler.Backend.Semantics.BviProps.AdjustOracleHOL
public import Flapjack.Compiler.Backend.Semantics.BviSem.Semantics
public import Flapjack.HolRef

@[expose] public section

/-!
# HOL `semantics_CURRY_I`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:962`: when
the source-side whole-program semantics does not fail, moving the compiler
configuration into `state_co` (with the unused compiler state kept in the
oracle by `state_cc`) leaves the observed behaviour unchanged. `CURRY I` is
written `Function.curry id`, as in the reviewed `stateCc`/`stateCo` rows.

The proof follows the source's shape. A non-failing source semantics has no
type-error result at any clock, so `evaluate_CURRY_I` applies at every clock:
the two initial runs agree in their result and FFI state. That makes the fail
conditions equivalent, the terminating observations pointwise equivalent and
the trace families equal, which is all `semantics_def` inspects.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Flapjack infrastructure: HOL `semantics_def` lists the state existential
before the result and outcome ones, while `terminatingObservation` keeps the
source order. This relates the two spellings so `terminatingObservation_unique`
applies to the `semantics_def` shape. -/
theorem terminatingObservation_iff {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (start : Nat) (behavior : HolBehaviour) :
    terminatingObservation ffi code oracle compiler start behavior ↔
      ∃ clock, ∃ state : BviState C F, ∃ result outcome,
        evaluateTuple ([.call 0 (some start) [] none], [],
          initialState ffi code oracle compiler clock) = (result, state) ∧
        (match result with
         | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
         | .val _ => outcome = HolOutcome.success
         | _ => False) ∧
        behavior = HolBehaviour.terminate outcome state.ffi.ioEvents := by
  constructor
  · rintro ⟨clock, result, state, outcome, run, ending, same⟩
    exact ⟨clock, state, result, outcome, run, ending, same⟩
  · rintro ⟨clock, state, result, outcome, run, ending, same⟩
    exact ⟨clock, result, state, outcome, run, ending, same⟩

@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "semantics_CURRY_I"]
theorem semantics_CURRY_I {C D F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle (C × D))
    (compiler : Compiler D) (start : Nat)
    (premise : semantics ffi code oracle
      (BackendProps.stateCc (Function.curry id) compiler) start ≠ .fail) :
    semantics ffi code oracle (BackendProps.stateCc (Function.curry id) compiler) start =
      semantics ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler start := by
  classical
  have hnoFailSource : ¬ (∃ clock error,
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock)).1 = .err error ∧
        error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) := by
    intro noFail
    apply premise
    rw [semantics_def]
    simp [noFail]
  have hnoType : ∀ clock,
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock)).1 ≠
        .err (.abort .typeError) := by
    intro clock same
    apply hnoFailSource
    exact ⟨clock, .abort .typeError, same, fun h => by simp at h, fun _ h => by simp at h⟩
  have htargetRun : ∀ clock, ∃ next : BviState D F,
      evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler clock) =
          ((evaluateTuple ([.call 0 (some start) [] none], [],
            initialState ffi code oracle
              (BackendProps.stateCc (Function.curry id) compiler) clock)).1, next) ∧
        next.ffi = (evaluateTuple ([.call 0 (some start) [] none], [],
          initialState ffi code oracle
            (BackendProps.stateCc (Function.curry id) compiler) clock)).2.ffi := by
    intro clock
    exact evaluate_CURRY_I [.call 0 (some start) [] none] [] ffi code oracle compiler clock
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock)).1
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock)).2
      ⟨rfl, hnoType clock⟩
  have htrace : ∀ clock,
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler
          clock)).2.ffi.ioEvents =
        (evaluateTuple ([.call 0 (some start) [] none], [],
          initialState ffi code oracle
            (BackendProps.stateCc (Function.curry id) compiler) clock)).2.ffi.ioEvents := by
    intro clock
    obtain ⟨next, sameRun, sameFfi⟩ := htargetRun clock
    simp only [sameRun, sameFfi]
  have failureEq : (∃ clock error,
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock)).1 = .err error ∧
        error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) ↔
      (∃ clock error,
        (evaluateTuple ([.call 0 (some start) [] none], [],
          initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler
            clock)).1 = .err error ∧
          error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) := by
    constructor
    · rintro ⟨clock, error, same, noTimeout, noFfi⟩
      obtain ⟨next, sameRun, _⟩ := htargetRun clock
      exact ⟨clock, error, by simpa only [sameRun] using same, noTimeout, noFfi⟩
    · rintro ⟨clock, error, same, noTimeout, noFfi⟩
      obtain ⟨next, sameRun, _⟩ := htargetRun clock
      exact ⟨clock, error, by simpa only [sameRun] using same, noTimeout, noFfi⟩
  let sourceTerm : HolBehaviour → Prop := fun behavior =>
    ∃ clock, ∃ state : BviState (C × D) F, ∃ result outcome,
      evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock) = (result, state) ∧
      (match result with
       | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
       | .val _ => outcome = HolOutcome.success
       | _ => False) ∧
      behavior = HolBehaviour.terminate outcome state.ffi.ioEvents
  let targetTerm : HolBehaviour → Prop := fun behavior =>
    ∃ clock, ∃ state : BviState D F, ∃ result outcome,
      evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler
          clock) = (result, state) ∧
      (match result with
       | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
       | .val _ => outcome = HolOutcome.success
       | _ => False) ∧
      behavior = HolBehaviour.terminate outcome state.ffi.ioEvents
  have sourceToTarget : ∀ behavior, sourceTerm behavior → targetTerm behavior := by
    rintro behavior ⟨clock, state, result, outcome, run, ending, same⟩
    obtain ⟨next, sameRun, sameFfi⟩ := htargetRun clock
    have sourceResult : (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle
        (BackendProps.stateCc (Function.curry id) compiler) clock)).1 = result := by
      rw [run]
    have sourceFfi : (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle
        (BackendProps.stateCc (Function.curry id) compiler) clock)).2 = state := by
      rw [run]
    exact ⟨clock, next, result, outcome, by
        rw [← sourceResult]
        exact sameRun, ending, by
        simp only [same, sourceFfi, sameFfi]⟩
  have targetToSource : ∀ behavior, targetTerm behavior → sourceTerm behavior := by
    rintro behavior ⟨clock, state, result, outcome, run, ending, same⟩
    obtain ⟨next, sameRun, sameFfi⟩ := htargetRun clock
    have pairEq : (result, state) = ((evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle
        (BackendProps.stateCc (Function.curry id) compiler) clock)).1, next) := by
      rw [← run]
      exact sameRun
    have resultEq : result = (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle
        (BackendProps.stateCc (Function.curry id) compiler) clock)).1 :=
      congrArg Prod.fst pairEq
    have stateEq : state = next := congrArg Prod.snd pairEq
    exact ⟨clock, (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code oracle
          (BackendProps.stateCc (Function.curry id) compiler) clock)).2, result, outcome,
      by
        rw [resultEq], ending, by
        simp only [same, stateEq, sameFfi]⟩
  have uniqueTarget : ∀ y z, targetTerm y → targetTerm z → y = z := by
    intro y z hy hz
    exact terminatingObservation_unique ffi code
      (BackendProps.stateCo (Function.curry id) oracle) compiler start y z
      ((terminatingObservation_iff ffi code
        (BackendProps.stateCo (Function.curry id) oracle) compiler start y).2 hy)
      ((terminatingObservation_iff ffi code
        (BackendProps.stateCo (Function.curry id) oracle) compiler start z).2 hz)
  have traceEq :
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluateTuple ([.call 0 (some start) [] none], [],
          initialState ffi code oracle
            (BackendProps.stateCc (Function.curry id) compiler) clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluateTuple ([.call 0 (some start) [] none], [],
          initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler
            clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor
    · rintro ⟨clock, same⟩
      exact ⟨clock, same.trans (congrArg HolLList.fromList (htrace clock).symm)⟩
    · rintro ⟨clock, same⟩
      exact ⟨clock, same.trans (congrArg HolLList.fromList (htrace clock))⟩
  simp only [semantics_def, failureEq, traceEq]
  by_cases hfail : (∃ clock error,
      (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi code (BackendProps.stateCo (Function.curry id) oracle) compiler
          clock)).1 = .err error ∧
        error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event))
  · simp only [if_pos hfail]
  · simp only [if_neg hfail]
    split
    · rename_i sourceSome
      split
      · rename_i targetSome
        exact uniqueTarget _ _
          (sourceToTarget _ (holOptionSome_some sourceSome))
          (holOptionSome_some targetSome)
      · rename_i targetNone
        exact absurd (sourceToTarget _ (holOptionSome_some sourceSome))
          (holOptionSome_none targetNone _)
    · rename_i sourceNone
      split
      · rename_i targetSome
        exact absurd (targetToSource _ (holOptionSome_some targetSome))
          (holOptionSome_none sourceNone _)
      · rfl

end Flapjack.Compiler.Backend.BviProps
