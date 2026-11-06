import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Observations
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateEventsClockFull
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateEventsClock

/-! Clock-indexed event chains for BVL-to-BVI divergence. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- Clock-indexed finite traces with a cofinal exact simulation have the same
lazy-list least upper bound. This is Flapjack proof infrastructure. -/
theorem clockTraceLub_eq {α : Type} (source target : Nat → List α)
    (sourceMono : ∀ clock extra, source clock <+: source (clock + extra))
    (targetMono : ∀ clock extra, target clock <+: target (clock + extra))
    (simulation : ∀ clock, ∃ extra, source clock = target (clock + extra)) :
    HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (source clock)) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (target clock)) := by
  let S := fun trace => ∃ clock, trace = HolLList.fromList (source clock)
  let T := fun trace => ∃ clock, trace = HolLList.fromList (target clock)
  have sourceChain : HolLList.lprefixChain S := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    rcases Nat.le_total i j with le | le
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
      exact Or.inl ((HolLList.lprefix_fromList _ _).2 (sourceMono i extra))
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
      exact Or.inr ((HolLList.lprefix_fromList _ _).2 (sourceMono j extra))
  have targetChain : HolLList.lprefixChain T := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    rcases Nat.le_total i j with le | le
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
      exact Or.inl ((HolLList.lprefix_fromList _ _).2 (targetMono i extra))
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
      exact Or.inr ((HolLList.lprefix_fromList _ _).2 (targetMono j extra))
  apply HolLList.IMP_build_lprefix_lub_EQ sourceChain targetChain
  · rintro _ ⟨clock, rfl⟩
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨HolLList.fromList (target (clock + extra)), ⟨clock + extra, rfl⟩, ?_⟩
    exact (HolLList.lprefix_fromList _ _).2 (by rw [equal])
  · rintro _ ⟨clock, rfl⟩
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨HolLList.fromList (source clock), ⟨clock, rfl⟩, ?_⟩
    exact (HolLList.lprefix_fromList _ _).2 (by rw [equal]; exact targetMono clock extra)

/-- Initial BVL and compiled BVI evaluations generate the same limit trace
when no source clock yields a type error. -/
theorem compileProgFuel_traceLub_eq {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (noTypeError : ∀ clock, (BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle
        (BackendProps.stateCc compileIncSource compiler) clock)).1 ≠ .err (.abort .typeError)) :
    HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList
      (BvlSem.evaluate [.call 0 (some start) []] [] (BvlSem.initialState ffi
        (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) clock)).2.ffi.ioEvents) =
    HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList
      (BviSem.evaluate [.call 0 (some targetStart) [] none] [] (BviSem.initialState ffi
        (sptFromAList targetProgram) (BackendProps.stateCo compileIncSource oracle) compiler clock)).2.ffi.ioEvents) := by
  apply clockTraceLub_eq
  · intro clock extra
    simpa [BvlSem.initialState] using BvlProps.evaluate_addClock_ioEvents_prefix
      [.call 0 (some start) []] [] (BvlSem.initialState ffi (sptFromAList programs)
        oracle (BackendProps.stateCc compileIncSource compiler) clock) extra
  · intro clock extra
    simpa [BviSem.initialState] using BviProps.evaluate_addClock_ioEvents_prefix
      [.call 0 (some targetStart) [] none] [] (BviSem.initialState ffi (sptFromAList targetProgram)
        (BackendProps.stateCo compileIncSource oracle) compiler clock) extra
  · intro clock
    let source := BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle
        (BackendProps.stateCc compileIncSource compiler) clock)
    have run : BvlSem.evaluate [.call 0 (some start) []] []
        (BvlSem.initialState ffi (sptFromAList programs) oracle
          (BackendProps.stateCc compileIncSource compiler) clock) = (source.1, source.2) := Prod.mk.eta.symm
    obtain ⟨extra, relocate, next, targetRun, related⟩ :=
      compileProgFuelEvaluate fuel optFuel start counter clock ffi programs oracle compiler
        targetStart targetNextName targetProgram source.1 source.2 compiled run distinct handlers
        oracleHandlers counterBound (noTypeError clock)
    refine ⟨extra, ?_⟩
    rw [targetRun]
    exact congrArg (·.ioEvents) related.2.1

/-- The executed BVL-to-BVI compiler preserves the entire whole-program
behavior of any non-failing source program. This remains untagged pending
source review of the BVI evaluator and dispatcher. -/
theorem compileProgFuel_semantics {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (nonfail : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler targetStart =
    BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start := by
  classical
  cases sourceBehavior : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start with
  | fail => exact False.elim (nonfail sourceBehavior)
  | terminate outcome events =>
    simpa [sourceBehavior] using compileProgFuel_semantics_of_terminates fuel optFuel start counter ffi programs oracle compiler
      targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound outcome events sourceBehavior
  | diverge trace =>
    have noTypeError := BvlSem.noTypeError_of_semantics_ne_fail ffi (sptFromAList programs)
      oracle (BackendProps.stateCc compileIncSource compiler) start nonfail
    have noFatal := compileProgFuel_noFatalError fuel optFuel start counter ffi programs oracle compiler
      targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound noTypeError
    have sourceNoObservation := BvlSem.no_terminatingObservation_of_semantics_eq_diverge ffi
      (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) start trace sourceBehavior
    have targetNoObservation : ∀ behavior, ¬ BviSem.terminatingObservation ffi (sptFromAList targetProgram)
        (BackendProps.stateCo compileIncSource oracle) compiler targetStart behavior := by
      intro behavior observed
      exact sourceNoObservation behavior (compileProgFuel_reflect_terminatingObservation fuel optFuel start counter
        ffi programs oracle compiler targetStart targetNextName targetProgram compiled distinct handlers
        oracleHandlers counterBound noTypeError behavior observed)
    have sourceNone : holOptionSome (BvlSem.terminatingObservation ffi (sptFromAList programs)
        oracle (BackendProps.stateCc compileIncSource compiler) start) = none := by
      unfold holOptionSome
      simp [not_exists.mpr sourceNoObservation]
    have targetNone : holOptionSome (BviSem.terminatingObservation ffi (sptFromAList targetProgram)
        (BackendProps.stateCo compileIncSource oracle) compiler targetStart) = none := by
      unfold holOptionSome
      simp [not_exists.mpr targetNoObservation]
    have traceEqual := compileProgFuel_traceLub_eq fuel optFuel start counter ffi programs oracle compiler
      targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound noTypeError
    have sourceTrace : HolBehaviour.diverge trace = HolBehaviour.diverge
        (HolLList.buildLprefixLub (fun tr => ∃ clock, tr = HolLList.fromList
          (BvlSem.evaluate [.call 0 (some start) []] [] (BvlSem.initialState ffi
            (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) clock)).2.ffi.ioEvents)) := by
      have h := sourceBehavior.symm
      simp only [BvlSem.semantics] at h
      rw [if_neg (not_exists.mpr noTypeError)] at h
      simpa only [sourceNone, BvlSem.evaluateTuple] using h
    simp only [BviSem.semantics, BviSem.evaluateTuple, noFatal, if_false, targetNone]
    exact (congrArg HolBehaviour.diverge traceEqual.symm).trans sourceTrace.symm

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
