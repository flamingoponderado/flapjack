import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownDriverSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.LoweringHandoff

/-! Known-function optimization followed by BVL and BVI lowering. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- The known-enabled closure driver, BVL optimizations and BVI lowering,
tail recursion, TMC and inlining preserve the current Lean observations under
the stated source, oracle, cache and counter conditions. This is Lean-side
pass composition rather than a standalone HOL declaration. Multi-argument and
direct-call conversion are disabled in this result. -/
theorem known_closure_optimized_bvi_semantics {C F : Type} (ffi : HolFfiState F)
    (closureFuel bvlFuel inlineLimit cutSize bviFuel optFuel : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (config output : Config) (knownConfig : ClosKnown.Config) (expressions : List ClosLang.Exp)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × OptimizationConfig C))) (compiler : BviSem.Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp)
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel bviFuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, final))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
              (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))))))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions ∧
      ∀ i, (oracle i).2.2 = [] ∧ ¬ containsAppSome config.maxApp (oracle i).2.1)
    (knownSafe :
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned expressions).2
      let globals := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).2
      syntaxOracleOk knownConfig numbered (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound :
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned expressions).1 ≤ (oracle 0).1.1)
    (cacheEq : ((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
      knownClosureFuture knownConfig oracle) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ ((knownClosureFuture knownConfig oracle) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace ((knownClosureFuture knownConfig oracle) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ ((knownClosureFuture knownConfig oracle) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace ((knownClosureFuture knownConfig oracle) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ ((knownClosureFuture knownConfig oracle) 0).1.2.1)
    (tailCounterBound : tailLast ≤ ((knownClosureFuture knownConfig oracle) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ ((knownClosureFuture knownConfig oracle) 0).1.2.2.2.1)
    (bviCacheEq : ((knownClosureFuture knownConfig oracle) 0).1.2.2.2.2.1 = bviCache) :
    BviSem.semantics ffi (sptFromAList final)
      (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
        (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
          (BvlInline.Proofs.letOpOracle splitSeq cutSize
            (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit
              (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ knownClosureFuture knownConfig oracle)))))))
      compiler targetStart =
    semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
              (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))))))) expressions := by
  let bvlOracle := pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ knownClosureFuture knownConfig oracle
  have closureEq := compileCallMtiFuel_knownOnly_semantics ffi closureFuel config output knownConfig expressions
    compiled names oracle (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)
    mti calls known positive closureRun nonfail numberSafe knownSafe oracleState initialBound
  have bvlNonfail : BvlSem.semantics ffi (sptFromAList compiled) bvlOracle
      (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler) output.start ≠ .fail := by
    rw [closureEq]
    exact nonfail
  have distinct := compileCallMtiFuel_knownOnly_labels closureFuel config output knownConfig expressions compiled names
    mti calls known closureRun
  have oracleDistinct : ∀ i, (((bvlOracle i).2).map Prod.fst).Nodup := by
    intro i
    simpa [bvlOracle, Function.comp_def, pureCo] using (knownClosureFuture_labels config.maxApp knownConfig oracle oracleState i).1
  have optimizedEq := BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_semantics bvlFuel inlineLimit cutSize bviFuel optFuel
    output.start 0 splitSeq tailEnabled tmcEnabled ffi compiled bvlOracle compiler cache optimized
    targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache optimizedRun lowerRun tailRun tmcRun inlineRun
    cacheEq distinct oracleDistinct oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker
    lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq bvlNonfail
  exact optimizedEq.trans closureEq

end Flapjack.Compiler.Backend.ClosToBvl
