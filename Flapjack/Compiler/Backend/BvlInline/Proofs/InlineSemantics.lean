import Flapjack.Compiler.Backend.BvlInline.Proofs.InitialState
import Flapjack.Compiler.Backend.BvlInline.Proofs.Semantics

/-! Whole-program observations for BVL tick inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

/-- Tick inlining preserves the whole-program BVL behavior when the source
does not fail. This corresponds to the local HOL semantics proof but remains
untagged: the state containing the finite reference map is internal to the
semantics and does not occur in this declaration's signature. -/
theorem inline_semantics {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (compiler : Compiler C)
    (start limit : Nat)
    (cacheEq : (oracle 0).1.1 = (tickCompileProg limit .ln program).1)
    (distinct : (program.map Prod.fst).Nodup)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle (inCc limit compiler) start ≠ .fail) :
    BvlSem.semantics ffi (sptFromAList (tickCompileProg limit .ln program).2)
      (inCo limit oracle) compiler start =
    BvlSem.semantics ffi (sptFromAList program) oracle (inCc limit compiler) start := by
  let source := initialObservation ffi (sptFromAList program) oracle (inCc limit compiler) start
  let target := initialObservation ffi (sptFromAList (tickCompileProg limit .ln program).2)
    (inCo limit oracle) compiler start
  have noType : ∀ clock, (source clock).1 ≠ .err (.abort .typeError) := by
    intro clock failure
    apply nonFail
    rw [semantics_eq_clockSemantics]
    change clockSemantics source = .fail
    simp [clockSemantics, failure, Exists.intro clock]
  have simulation : ∀ clock, ∃ extra, source clock = target (clock + extra) := by
    intro clock
    let sourceState := initialState ffi (sptFromAList program) oracle (inCc limit compiler) clock
    let run := evaluateTuple ([.call 0 (some start) []], [], sourceState)
    have valid : run.1 ≠ .err (.abort .typeError) := by
      simpa [run, sourceState, source, initialObservation, evaluateTuple] using noType clock
    obtain ⟨targetFinal, targetRun, ffiEq⟩ :=
      inEvaluateCall limit start clock [] ffi program oracle compiler run.1 run.2
        ⟨by simp [run, sourceState], cacheEq, distinct, valid⟩
    change evaluate [.call 0 (some start) []] []
      (initialState ffi (sptFromAList (tickCompileProg limit .ln program).2)
        (inCo limit oracle) compiler clock) = (run.1, targetFinal) at targetRun
    refine ⟨0, ?_⟩
    change (run.1, run.2.ffi.ioEvents) = _
    simp [target, initialObservation, targetRun, ffiEq]
  have same : clockSemantics source = clockSemantics target := by
    apply clockSemantics_eq
    · exact initialObservation_stable _ _ _ _ _
    · exact initialObservation_monotone _ _ _ _ _
    · exact initialObservation_monotone _ _ _ _ _
    · exact simulation
  rw [semantics_eq_clockSemantics, semantics_eq_clockSemantics]
  exact same.symm

end Flapjack.Compiler.Backend.BvlInline.Proofs
