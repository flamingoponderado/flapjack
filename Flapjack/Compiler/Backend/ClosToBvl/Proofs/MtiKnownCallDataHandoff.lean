import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiKnownCallLoweringHandoff
import Flapjack.Compiler.Backend.BviToData.Proofs.Semantics
import Flapjack.Compiler.Backend.BviToData.Proofs.CompileAgreement

/-! All closure optimizations followed by BVI-to-data conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- Incremental BVI oracle after the selected closure and BVL/BVI passes. -/
noncomputable abbrev mtiKnownCallBviOracle {C : Type} (fuel maxApp inlineLimit cutSize : Nat)
    (splitSeq tailEnabled tmcEnabled : Bool) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C)))) :
    BviSem.CompileOracle C :=
  stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
    (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
      (BvlInline.Proofs.letOpOracle splitSeq cutSize
        (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit
          (pureCo (compileInc maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
            mtiKnownCallFuture fuel maxApp knownConfig oracle))))))

/-- Compose the all-optimizations closure and BVI proof with the BVI-to-data
simulation, and identify the executed bounded data pass with the simulated
program. Source, oracle, cache, and counter assumptions remain explicit;
this is Flapjack-specific composition infrastructure. -/
theorem mti_known_call_closure_optimized_data_semantics {C F : Type} (ffi : HolFfiState F)
    (closureFuel relationFuel bvlFuel inlineLimit cutSize bviFuel optFuel : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (config output : Config) (knownConfig : ClosKnown.Config) (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C)))) (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (enabled : config.doMti = true) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp) (nonempty : expressions ≠ [])
    (unary : ∀ e ∈ expressions, noMti e)
    (oracleUnary : ∀ i, (oracle i).2.2 = [] ∧ ∀ e ∈ (oracle i).2.1, noMti e)
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel bviFuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, final))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc (ClosMti.compileInc config.maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (ClosCall.compileIncFuelCallback closureFuel (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
              (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled
                (fun cfg code => compiler cfg (BviToData.compileProg code)))))))))))) expressions ≠ .fail)
    (knownSafe :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let globals := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).2
      syntaxOracleOk knownConfig numbered (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCo (ClosMti.compileInc config.maxApp) ∘ oracle)) globals)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ oracle))
    (initialBound :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned transformed).1 ≤ (oracle 0).1.1)
    (callRun :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel closureFuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState))
    (knownState : callState.1 = (knownClosureFuture knownConfig
      (pureCo (ClosMti.compileInc config.maxApp) ∘ oracle) 0).1.1)
    (cacheEq : ((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
      mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) 0).1.2.1)
    (tailCounterBound : tailLast ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) 0).1.2.2.2.1)
    (bviCacheEq : ((mtiKnownCallFuture closureFuel config.maxApp knownConfig oracle) 0).1.2.2.2.2.1 = bviCache) :
    let bviOracle := mtiKnownCallBviOracle closureFuel config.maxApp inlineLimit cutSize
      splitSeq tailEnabled tmcEnabled knownConfig oracle
    DataSem.semantics ffi (sptFromAList (BviToData.compileProg final))
      (fun n => let (cfg, code) := bviOracle n; (cfg, BviToData.compileProg code))
      compiler limits sizes targetStart =
    semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc (ClosMti.compileInc config.maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (ClosCall.compileIncFuelCallback closureFuel (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
              (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled
                (fun cfg code => compiler cfg (BviToData.compileProg code)))))))))))) expressions ∧
      (final.mapM fun (name, argc, body) => do
        pure (name, argc, ← BviToData.compileExpBounded bviFuel argc body)) =
        some (BviToData.compileProg final) := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let bviOracle := mtiKnownCallBviOracle closureFuel config.maxApp inlineLimit cutSize
    splitSeq tailEnabled tmcEnabled knownConfig oracle
  have behavior := mti_known_call_closure_optimized_bvi_semantics ffi
    closureFuel relationFuel bvlFuel inlineLimit cutSize bviFuel optFuel splitSeq tailEnabled tmcEnabled
    config output knownConfig expressions called callState compiled names oracle bviCompiler cache optimized
    targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache
    enabled calls known positive nonempty unary oracleUnary closureRun optimizedRun lowerRun tailRun tmcRun inlineRun
    nonfail knownSafe oracleState initialBound callRun knownState cacheEq oracleTailBound oracleTailWorker
    oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  have noFail : BviSem.semantics ffi (sptFromAList final) bviOracle bviCompiler targetStart ≠ .fail := by
    rw [behavior]
    exact nonfail
  have agreement := BviToData.compileProg_semantics ffi final bviOracle compiler limits sizes targetStart noFail
  constructor
  · exact agreement.trans behavior
  · exact BviToData.compileProgBounded_agrees bviFuel final

end Flapjack.Compiler.Backend.ClosToBvl
