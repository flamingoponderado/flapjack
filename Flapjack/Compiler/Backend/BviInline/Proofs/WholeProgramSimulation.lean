import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksInduction

/-! Whole-program execution through BVI inlining and tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem

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

/-- Flapjack infrastructure: an initial call through tick-cleaned code is
reproduced by the original code with extra clock and the same final FFI. -/
theorem evaluate_removeTicks_compile {C F : Type} (program : List (Nat × Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle C) (compiler : BviSem.Compiler C)
    (ffi : HolFfiState F) (clock start : Nat) (result : BviResult) (targetNext : BviState C F)
    (run : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock) =
        (result, targetNext)) :
    ∃ extra sourceNext, evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (removeTicksCc compiler) (clock + extra)) =
        (result, sourceNext) ∧ sourceNext.ffi = targetNext.ffi := by
  have related := removeStateRel_initial program oracle compiler ffi clock
  have cleanedRun : evaluate (removeTicksListSource [.call 0 (some start) [] none]) []
      (initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock) =
        (result, targetNext) := by simpa [removeTicksListSource, removeTicksSource] using run
  obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ :=
    RemoveTicksCases.evaluate_removeTicks [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock)
      (initialState ffi (sptFromAList program) oracle (removeTicksCc compiler) clock)
      result targetNext related cleanedRun
  exact ⟨extra, sourceNext, by simpa [initialState] using sourceRun, finalRel.2.2.2.1.symm⟩

/-- Flapjack infrastructure: the whole executed inlining and tick-cleanup
pipeline reproduces the optimized initial call with extra clock when the
source does not type-error at any clock. The safety premise is the original
whole-program theorem's premise; HOL carrier review remains pending. -/
theorem evaluate_compileProgFuel {C F : Type} (fuel : Nat)
    (program intermediate : List (Nat × Nat × Bvi.Exp)) (cache : Spt (Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C))
    (compiler : BviSem.Compiler C) (ffi : HolFfiState F) (clock start : Nat)
    (result : BviResult) (targetNext : BviState C F)
    (inlined : inlineAllFuel fuel .ln program = some (cache, intermediate))
    (oracleCache : (oracle 0).1.1 = cache) (distinct : (program.map Prod.fst).Nodup)
    (safe : ∀ clock', (evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (inCc (removeTicksCc compiler)) clock')).1 ≠
        .err (.abort .typeError))
    (run : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList (cleanProg intermediate)) (removeTicksCo (inCo oracle)) compiler clock) =
        (result, targetNext)) :
    ∃ extra sourceNext, evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (inCc (removeTicksCc compiler)) (clock + extra)) =
        (result, sourceNext) ∧ sourceNext.ffi = targetNext.ffi := by
  obtain ⟨extra, intermediateNext, intermediateRun, intermediateFfi⟩ :=
    evaluate_removeTicks_compile intermediate (inCo oracle) compiler ffi clock start result targetNext run
  let source := initialState ffi (sptFromAList program) oracle (inCc (removeTicksCc compiler)) (clock + extra)
  cases sourceRun : evaluate [.call 0 (some start) [] none] [] source with
  | mk sourceResult sourceNext =>
    have sourceNotType : sourceResult ≠ .err (.abort .typeError) := by
      have h := safe (clock + extra)
      simpa [source, sourceRun] using h
    obtain ⟨targetState, targetRun, finalRel⟩ :=
      evaluate_inlineFuel_compile fuel program intermediate cache oracle ffi (removeTicksCc compiler)
        (clock + extra) start sourceResult sourceNext inlined oracleCache distinct sourceRun sourceNotType
    rw [intermediateRun] at targetRun
    have equal := Prod.mk.inj targetRun.symm
    obtain ⟨resultEq, stateEq⟩ := equal
    subst sourceResult
    subst targetState
    exact ⟨extra, sourceNext, sourceRun, finalRel.2.2.2.1.symm.trans intermediateFfi⟩

/-- Flapjack infrastructure: the production whole-program compiler result
has the initial-call simulation with the incremental callback and oracle.
This remains untagged pending source review of the evaluator and carriers. -/
theorem evaluate_compileProgFuel_result {C F : Type} (fuel : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (cache : Spt (Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C))
    (compiler : BviSem.Compiler C) (ffi : HolFfiState F) (clock start : Nat)
    (result : BviResult) (targetNext : BviState C F)
    (compiled : compileProgFuel fuel program = some (cache, output))
    (oracleCache : (oracle 0).1.1 = cache) (distinct : (program.map Prod.fst).Nodup)
    (safe : ∀ clock', (evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (BackendProps.stateCc compileIncSource compiler) clock')).1 ≠
        .err (.abort .typeError))
    (run : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList output) (BackendProps.stateCo compileIncSource oracle) compiler clock) =
        (result, targetNext)) :
    ∃ extra sourceNext, evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (BackendProps.stateCc compileIncSource compiler) (clock + extra)) =
        (result, sourceNext) ∧ sourceNext.ffi = targetNext.ffi := by
  cases inlineSource : inlineAllSource .ln program with
  | mk finalCache intermediate =>
    have inlined : inlineAllFuel fuel .ln program = some (finalCache, intermediate) := by
      simpa [inlineSource] using inlineAllFuel_eq_source fuel .ln program
    have resultEq : (finalCache, cleanProg intermediate) = (cache, output) := by
      have actual := compileProgFuel_tick_cleanup fuel program intermediate finalCache inlined
      rw [compiled] at actual
      exact (Option.some.inj actual).symm
    obtain ⟨rfl, rfl⟩ := resultEq
    apply evaluate_compileProgFuel fuel program intermediate cache oracle compiler ffi clock start result targetNext
      inlined oracleCache distinct
    · simpa [stateCc_compileIncSource] using safe
    · simpa [stateCo_compileIncSource] using run

end Flapjack.Compiler.Backend.BviInline
