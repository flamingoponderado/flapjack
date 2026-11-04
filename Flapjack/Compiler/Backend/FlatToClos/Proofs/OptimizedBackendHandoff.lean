import Flapjack.Compiler.Backend.FlatToClos.Proofs.BackendHandoff
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiKnownCallDataHandoff

/-! CakeML source behavior through all closure optimizations and BVI. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosToBvl Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.ClosProps Flapjack.Compiler.Backend.ClosKnown

local instance {C : Type} [Nonempty C] : Nonempty (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C))) :=
  ⟨(0, .ln, .ln, .ln, 0, 0, 0, .ln, Classical.choice ‹Nonempty C›)⟩

/-- Callback matching the closure and backend passes in this composition. -/
noncomputable abbrev allClosureCompiler {C : Type} (fuel maxApp inlineLimit cutSize : Nat)
    (splitSeq tailEnabled tmcEnabled : Bool) (knownConfig : ClosKnown.Config) (compiler : BviSem.Compiler C) :
    ClosSem.Compiler (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C))) :=
  pureCc (ClosMti.compileInc maxApp)
    (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
        (pureCc ticksInc (pureCc letopInc
          (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
            (pureCc (compileInc maxApp) (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))))))))

/-- CakeML source behavior through all closure optimizations and BVI lowering.
The source precondition, callback relation, oracle, cache, and counter conditions
remain explicit; this is Flapjack-specific composition infrastructure. -/
theorem cakeToAllOptimizedBvi_semantics {C F : Type} [Nonempty C]
    (interp : Option (SemanticPrimitivesHOL.Value → Option (SourceToFlat.Config × (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C))))))
    (source : SemanticPrimitivesHOL.State F) (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceConfig nextSource : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C))))
    (declarations : List AstHOL.Dec)
    (closureFuel relationFuel bvlFuel inlineLimit cutSize bviFuel optFuel : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (config output : ClosToBvl.Config) (knownConfig : ClosKnown.Config) (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (compiler : BviSem.Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (enabled : config.doMti = true) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp)
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (allClosureCompiler closureFuel config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled knownConfig compiler))
    (sourceRun : SourceToFlat.compileCakeToClosFuel closureFuel sourceConfig declarations = some (nextSource, expressions))
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel bviFuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, final))
    (knownSafe :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let globals := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).2
      syntaxOracleOk knownConfig numbered (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCo (ClosMti.compileInc config.maxApp) ∘ (sourceClosureOracle flatConfig))) globals)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ (sourceClosureOracle flatConfig)))
    (initialBound :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned transformed).1 ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (callRun :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel closureFuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState))
    (knownState : callState.1 = (knownClosureFuture knownConfig
      (pureCo (ClosMti.compileInc config.maxApp) ∘ (sourceClosureOracle flatConfig)) 0).1.1)
    (cacheEq : ((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
      mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.1)
    (tailCounterBound : tailLast ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.2.2.1)
    (bviCacheEq : ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.2.2.2.1 = bviCache) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (BviSem.semantics source.ffi (sptFromAList final)
        (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
          (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
            (BvlInline.Proofs.letOpOracle splitSeq cutSize
              (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit
                (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
                  mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig))))))))
        compiler targetStart) := by
  let intermediate := allClosureCompiler closureFuel config.maxApp inlineLimit cutSize
    splitSeq tailEnabled tmcEnabled knownConfig compiler
  have sourceBehavior := cakeCompileToClosFuel_semantics_exists closureFuel interp source sourceEnv sourceConfig nextSource
    flatConfig intermediate declarations expressions config.maxApp precondition safe positive production sourceRun
  have nonfail : ClosSem.semantics source.ffi config.maxApp HolFiniteMapExact.holEmpty
      (sourceClosureOracle flatConfig) intermediate expressions ≠ .fail := by
    intro failure
    change ClosSem.semantics source.ffi config.maxApp HolFiniteMapExact.empty
      (sourceClosureOracle flatConfig) intermediate expressions = .fail at failure
    rw [failure] at sourceBehavior
    exact safe sourceBehavior
  have unary := sourceClosure_noMti closureFuel sourceConfig nextSource declarations expressions sourceRun
  have nonempty := sourceClosure_nonempty closureFuel sourceConfig nextSource declarations expressions sourceRun
  have oracleUnary : ∀ index, ((sourceClosureOracle flatConfig) index).2.2 = [] ∧
      ∀ e ∈ ((sourceClosureOracle flatConfig) index).2.1, noMti e := by
    intro index
    change (incCompileDecs (flatConfig.compileOracle index).2).2 = [] ∧
      ∀ e ∈ (incCompileDecs (flatConfig.compileOracle index).2).1, noMti e
    exact ⟨rfl, incCompileDecs_noMti _⟩
  have backend := mti_known_call_closure_optimized_bvi_semantics source.ffi
    closureFuel relationFuel bvlFuel inlineLimit cutSize bviFuel optFuel splitSeq tailEnabled tmcEnabled
    config output knownConfig expressions called callState compiled names (sourceClosureOracle flatConfig) compiler
    cache optimized targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache
    enabled calls known positive nonempty unary oracleUnary closureRun optimizedRun lowerRun tailRun tmcRun inlineRun
    nonfail knownSafe oracleState initialBound callRun knownState cacheEq oracleTailBound oracleTailWorker
    oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  rw [backend]
  exact sourceBehavior

/-- Compose CakeML source behavior through the all-optimizations path and
BVI-to-data semantics, with bounded data compilation agreement. -/
theorem cakeToAllOptimizedData_semantics {C F : Type} [Nonempty C]
    (interp : Option (SemanticPrimitivesHOL.Value → Option (SourceToFlat.Config × (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C))))))
    (source : SemanticPrimitivesHOL.State F) (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceConfig nextSource : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × (Spt ValApprox × (NumSet × OptimizationConfig C))))
    (declarations : List AstHOL.Dec)
    (closureFuel relationFuel bvlFuel inlineLimit cutSize bviFuel optFuel : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (config output : ClosToBvl.Config) (knownConfig : ClosKnown.Config) (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (enabled : config.doMti = true) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp)
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (allClosureCompiler closureFuel config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled knownConfig
        (fun cfg code => compiler cfg (BviToData.compileProg code))))
    (sourceRun : SourceToFlat.compileCakeToClosFuel closureFuel sourceConfig declarations = some (nextSource, expressions))
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel bviFuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, final))
    (knownSafe :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let globals := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).2
      syntaxOracleOk knownConfig numbered (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCo (ClosMti.compileInc config.maxApp) ∘ (sourceClosureOracle flatConfig))) globals)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ (sourceClosureOracle flatConfig)))
    (initialBound :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned transformed).1 ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (callRun :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel closureFuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState))
    (knownState : callState.1 = (knownClosureFuture knownConfig
      (pureCo (ClosMti.compileInc config.maxApp) ∘ (sourceClosureOracle flatConfig)) 0).1.1)
    (cacheEq : ((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
      mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.1)
    (tailCounterBound : tailLast ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.2.2.1)
    (bviCacheEq : ((mtiKnownCallFuture closureFuel config.maxApp knownConfig (sourceClosureOracle flatConfig)) 0).1.2.2.2.2.1 = bviCache) :
    let bviOracle := mtiKnownCallBviOracle closureFuel config.maxApp inlineLimit cutSize
      splitSeq tailEnabled tmcEnabled knownConfig (sourceClosureOracle flatConfig)
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (DataSem.semantics source.ffi (sptFromAList (BviToData.compileProg final))
        (fun n => let (cfg, code) := bviOracle n; (cfg, BviToData.compileProg code))
        compiler limits sizes targetStart) ∧
      (final.mapM fun (name, argc, body) => do
        pure (name, argc, ← BviToData.compileExpBounded bviFuel argc body)) =
        some (BviToData.compileProg final) := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let bviOracle := mtiKnownCallBviOracle closureFuel config.maxApp inlineLimit cutSize
    splitSeq tailEnabled tmcEnabled knownConfig (sourceClosureOracle flatConfig)
  have behavior := cakeToAllOptimizedBvi_semantics interp source sourceEnv sourceConfig nextSource flatConfig declarations
    closureFuel relationFuel bvlFuel inlineLimit cutSize bviFuel optFuel splitSeq tailEnabled tmcEnabled
    config output knownConfig expressions called callState compiled names bviCompiler cache optimized
    targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache
    enabled calls known positive precondition safe production sourceRun closureRun optimizedRun lowerRun tailRun tmcRun inlineRun
    knownSafe oracleState initialBound callRun knownState cacheEq oracleTailBound oracleTailWorker
    oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  have noFail : BviSem.semantics source.ffi (sptFromAList final) bviOracle bviCompiler targetStart ≠ .fail := by
    intro failure
    apply safe
    simpa [bviOracle, mtiKnownCallBviOracle, bviCompiler, failure] using behavior
  have agreement := BviToData.compileProg_semantics source.ffi final bviOracle compiler limits sizes targetStart noFail
  constructor
  · rw [agreement]
    exact behavior
  · exact BviToData.compileProgBounded_agrees bviFuel final

end Flapjack.Compiler.Backend.FlatToClos
