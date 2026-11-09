import Flapjack.Compiler.Backend.BvlInline.Proofs.CompileProg
import Flapjack.Compiler.Backend.BvlInline.Proofs.ClockedObservations
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateEventsClock
import Flapjack.Compiler.Backend.Semantics.BvlSem.Semantics

/-! Whole-program observations for BVL tick removal. These declarations are
Flapjack infrastructure; the HOL semantics theorem is not yet classified as a
port because its internal BVL state uses a finite-map representation that is
not exposed in the theorem's signature. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.Compiler.Backend.BvlProps
open Flapjack.SemanticPrimitivesHOL

/-- The result and event trace of an initial BVL call at a given clock. -/
noncomputable def initialObservation {C F : Type} (ffi : HolFfiState F)
    (program : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start clock : Nat) :
    ClockObservation (List BvlSem.Value) BvlSem.Value :=
  let run := evaluate [.call 0 (some start) []] []
    (initialState ffi program oracle compiler clock)
  (run.1, run.2.ffi.ioEvents)

/-- The clock-indexed BVL observations are stable after a non-timeout result. -/
theorem initialObservation_stable {C F : Type} (ffi : HolFfiState F)
    (program : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    clockStable (initialObservation ffi program oracle compiler start) := by
  intro clock extra notTimeout
  let state := initialState ffi program oracle compiler clock
  let run := evaluate [.call 0 (some start) []] [] state
  have shifted := evaluate_addClock [.call 0 (some start) []] [] state run.2 run.1 extra
    (by simp [run]) notTimeout
  simpa [initialObservation, state, run, initialState] using
    congrArg (fun output => (output.1, output.2.ffi.ioEvents)) shifted

/-- Increasing the initial clock extends the observed event trace. -/
theorem initialObservation_monotone {C F : Type} (ffi : HolFfiState F)
    (program : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    clockMonotone (initialObservation ffi program oracle compiler start) := by
  intro clock later le
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  simpa [initialObservation, initialState] using
    evaluate_addClock_ioEvents_prefix [.call 0 (some start) []] []
      (initialState ffi program oracle compiler clock) extra

/-- Tick removal preserves the complete clock-indexed BVL behavior. This
factored statement is Flapjack infrastructure for the whole-program proof. -/
theorem removeTicks_observations {C F : Type} (ffi : HolFfiState F)
    (program : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    clockSemantics (initialObservation ffi
      (sptMap (fun (arity, body) => (arity, removeTicksSing body)) program)
      (removeTicksCo ∘ oracle) compiler start) =
    clockSemantics (initialObservation ffi program oracle (removeTicksCc compiler) start) := by
  apply clockSemantics_eq
  · exact initialObservation_stable _ _ _ _ _
  · exact initialObservation_monotone _ _ _ _ _
  · exact initialObservation_monotone _ _ _ _ _
  · intro clock
    let run := evaluateTuple ([.call 0 (some start) []], [],
      initialState ffi (sptMap (fun (arity, body) => (arity, removeTicksSing body)) program)
        (removeTicksCo ∘ oracle) compiler clock)
    obtain ⟨extra, final, sourceRun, ffiEq⟩ :=
      evaluateCompileProg ffi program oracle compiler clock start run.1 run.2 (by simp [run])
    refine ⟨extra, ?_⟩
    change (run.1, run.2.ffi.ioEvents) = _
    change evaluate [.call 0 (some start) []] []
      (initialState ffi program oracle (removeTicksCc compiler) (clock + extra)) = _ at sourceRun
    simp [initialObservation, sourceRun, ffiEq]

/-- The source-shaped whole-program behavior equals the factored clocked
observation behavior. This is a Flapjack-specific decomposition lemma. -/
theorem semantics_eq_clockSemantics {C F : Type} (ffi : HolFfiState F)
    (program : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    BvlSem.semantics ffi program oracle compiler start =
      clockSemantics (initialObservation ffi program oracle compiler start) := by
  classical
  have terminating : BvlSem.terminatingObservation ffi program oracle compiler start =
      clockTerminating (initialObservation ffi program oracle compiler start) := by
    funext behavior
    apply propext
    unfold BvlSem.terminatingObservation clockTerminating
    constructor
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      refine ⟨clock, result, outcome, ?_, ?_, ?_⟩
      · change (evaluateTuple ([.call 0 (some start) []], [],
          initialState ffi program oracle compiler clock)).1 = result
        simp [run]
      · cases result with
        | val _ => simpa using outcomeEq
        | err error => cases error with
          | raise _ => simpa using outcomeEq
          | abort abort => cases abort <;> simp_all
      · change behavior = HolBehaviour.terminate outcome
          (evaluateTuple ([.call 0 (some start) []], [],
            initialState ffi program oracle compiler clock)).2.ffi.ioEvents
        simpa [run] using behaviorEq
    · rintro ⟨clock, result, outcome, resultEq, outcomeEq, behaviorEq⟩
      let run := evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi program oracle compiler clock)
      refine ⟨clock, result, run.2, outcome, ?_, ?_, ?_⟩
      · change run = (result, run.2)
        apply Prod.ext
        · simpa [run, initialObservation, evaluateTuple] using resultEq
        · rfl
      · cases result with
        | val _ => simpa using outcomeEq
        | err error => cases error with
          | raise _ => simpa using outcomeEq
          | abort abort => cases abort <;> simp_all
      · simpa [run, initialObservation, evaluateTuple] using behaviorEq
  unfold BvlSem.semantics clockSemantics
  simp only [terminating, initialObservation, evaluateTuple]
  rfl

/-- Tick removal preserves the entire BVL whole-program behavior. This
Flapjack theorem is untagged until the internally used finite-map state has a
reviewed HOL reference qualifier for declarations without state parameters. -/
theorem removeTicks_semantics {C F : Type} (ffi : HolFfiState F)
    (program : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    BvlSem.semantics ffi
      (sptMap (fun (arity, body) => (arity, removeTicksSing body)) program)
      (removeTicksCo ∘ oracle) compiler start =
    BvlSem.semantics ffi program oracle (removeTicksCc compiler) start := by
  simp only [semantics_eq_clockSemantics]
  exact removeTicks_observations ffi program oracle compiler start

end Flapjack.Compiler.Backend.BvlInline.Proofs
