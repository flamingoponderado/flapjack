module

public import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksInduction

@[expose] public section

/-! Whole-program execution through BVI inlining and tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem

namespace InitialStateCarrier
/-- The canonical BVI reference-map representation has a roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end InitialStateCarrier

/-- Flapjack infrastructure: the incremental compiler callback factors into
inlining followed by tick cleanup. -/
theorem stateCc_compileIncSource {C : Type} (compiler : BviSem.Compiler C) :
    BackendProps.stateCc compileIncSource compiler = inCc (removeTicksCc compiler) := by
  funext config program
  obtain ⟨cache, downstream⟩ := config
  cases inlineRun : inlineAllSource cache program with
  | mk next output =>
    simp [inCc, removeTicksCc, BackendProps.stateCc, compileIncSource, cleanProg, inlineRun]

/-- Flapjack infrastructure: the incremental oracle factors through the
inlining oracle followed by tick cleanup. -/
theorem stateCo_compileIncSource {C : Type}
    (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C)) :
    BackendProps.stateCo compileIncSource oracle = removeTicksCo (inCo oracle) := by
  funext index
  simp [BackendProps.stateCo, compileIncSource, removeTicksCo, inCo, cleanProg]

/-- An initial call through tick-cleaned code is reproduced by the original
code with extra clock and the same final FFI. The evaluator inherits the
real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_remove_ticks_compile"
  (fmap_as_finite_support := [refs])]
theorem evaluate_removeTicks_compile {C F : Type} (program : List (Nat × Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle C) (ffi : HolFfiState F) (compiler : BviSem.Compiler C)
    (clock start : Nat) (result : BviResult) (targetNext : BviState C F)
    (run : evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock) =
        (result, targetNext)) :
    ∃ extra sourceNext, evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi (sptFromAList program) oracle (removeTicksCc compiler) (clock + extra)) =
        (result, sourceNext) ∧ sourceNext.ffi = targetNext.ffi := by
  have related := removeStateRel_initial program oracle compiler ffi clock
  have cleanedRun : evaluate (removeTicksListSource [.call 0 (some start) [] none]) []
      (initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock) =
        (result, targetNext) := by simpa [evaluateTuple, removeTicksListSource, removeTicksSource] using run
  obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ :=
    RemoveTicksCases.evaluate_removeTicks [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock)
      (initialState ffi (sptFromAList program) oracle (removeTicksCc compiler) clock)
      result targetNext related cleanedRun
  exact ⟨extra, sourceNext, by simpa [evaluateTuple, initialState] using sourceRun, finalRel.2.2.2.1.symm⟩

/-- The complete initial-call simulation for source-shaped whole-program
inlining, with the original all-clock type-error exclusion. The evaluator
inherits the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_compile_prog"
  (fmap_as_finite_support := [refs])]
theorem evaluateCompileProg {C F : Type}
    (program : List (Nat × Nat × Bvi.Exp)) (cache : Spt (Nat × Bvi.Exp))
    (output : List (Nat × Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C))
    (ffi : HolFfiState F) (compiler : BviSem.Compiler C) (clock start : Nat)
    (result : BviResult) (targetNext : BviState C F)
    (premises : compileProgSource program = (cache, output) ∧
      (oracle 0).1.1 = cache ∧ (program.map Prod.fst).Nodup ∧
      (∀ j, (evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi (sptFromAList program) oracle
          (BackendProps.stateCc compileIncSource compiler) j)).1 ≠ .err (.abort .typeError)) ∧
      evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi (sptFromAList output) (BackendProps.stateCo compileIncSource oracle)
          compiler clock) = (result, targetNext)) :
    ∃ extra sourceNext,
      evaluateTuple ([.call 0 (some start) [] none], [],
        initialState ffi (sptFromAList program) oracle
          (BackendProps.stateCc compileIncSource compiler) (clock + extra)) = (result, sourceNext) ∧
      sourceNext.ffi = targetNext.ffi := by
  obtain ⟨compiled, oracleCache, distinct, safe, run⟩ := premises
  cases inlineSource : inlineAllSource .ln program with
  | mk finalCache intermediate =>
    have resultEq : (finalCache, cleanProg intermediate) = (cache, output) := by
      simpa [compileProgSource, compileIncSource, inlineSource, cleanProg] using compiled
    obtain ⟨rfl, rfl⟩ := resultEq
    have safe' : ∀ j, (evaluate [.call 0 (some start) [] none] []
        (initialState ffi (sptFromAList program) oracle (inCc (removeTicksCc compiler)) j)).1 ≠
          .err (.abort .typeError) := by
      simpa [evaluateTuple, stateCc_compileIncSource] using safe
    have run' : evaluate [.call 0 (some start) [] none] []
        (initialState ffi (sptFromAList (cleanProg intermediate)) (removeTicksCo (inCo oracle)) compiler clock) =
          (result, targetNext) := by
      simpa [evaluateTuple, stateCo_compileIncSource] using run
    obtain ⟨extra, intermediateNext, intermediateRun, intermediateFfi⟩ :=
      evaluate_removeTicks_compile intermediate (inCo oracle) ffi compiler clock start result targetNext run'
    simp only [evaluateTuple] at intermediateRun
    let source := initialState ffi (sptFromAList program) oracle (inCc (removeTicksCc compiler)) (clock + extra)
    cases sourceRun : evaluate [.call 0 (some start) [] none] [] source with
    | mk sourceResult sourceNext =>
      have sourceNotType : sourceResult ≠ .err (.abort .typeError) := by
        have h := safe' (clock + extra)
        simpa [source, sourceRun] using h
      obtain ⟨targetState, targetRun, finalRel⟩ :=
        evaluate_inline_compile program intermediate cache oracle ffi (removeTicksCc compiler)
          (clock + extra) start sourceResult sourceNext inlineSource oracleCache distinct sourceRun sourceNotType
      rw [intermediateRun] at targetRun
      have equal := Prod.mk.inj targetRun.symm
      obtain ⟨resultEq, stateEq⟩ := equal
      subst sourceResult
      subst targetState
      exact ⟨extra, sourceNext, by simpa [evaluateTuple, stateCc_compileIncSource] using sourceRun,
        finalRel.2.2.2.1.symm.trans intermediateFfi⟩

end Flapjack.Compiler.Backend.BviInline
