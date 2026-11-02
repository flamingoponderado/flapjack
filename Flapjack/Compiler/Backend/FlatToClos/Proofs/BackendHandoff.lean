import Flapjack.Compiler.Backend.FlatToClos.Proofs.SourcePreprocessing
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.LoweringHandoff
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi

/-! Conditional source-to-BVI behavior composition. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosToBvl

local instance {C : Type} [Nonempty C] : Nonempty (Nat × OptimizationConfig C) :=
  ⟨(0, .ln, 0, 0, 0, .ln, Classical.choice ‹Nonempty C›)⟩

/-- The closure oracle supplied by the source-to-flat installation configuration. -/
noncomputable abbrev sourceClosureOracle {C : Type} (config : FlatSem.InstallConfig C) : ClosSem.CompileOracle C :=
  pureCo incCompileDecs ∘ config.compileOracle

/-- The source compiler callback for the proved closure and BVL/BVI stages. -/
noncomputable abbrev sourceClosureCompiler {C : Type} (maxApp inlineLimit cutSize : Nat)
    (splitSeq tailEnabled tmcEnabled : Bool) (compiler : BviSem.Compiler C) :
    ClosSem.Compiler (Nat × OptimizationConfig C) :=
  stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc
    (pureCc (compileInc maxApp) (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))

/-- The source-to-closure compiler, the production closure driver with its
optional optimizations disabled, and the implemented BVL/BVI pipeline produce
an observable behavior of the original CakeML declarations. The source pass,
compiler-oracle and cache premises are explicit, and the proof-side semantics
and carriers still require review against HOL. -/
theorem cakeToOptimizedBvi_semantics_proofSide {C F : Type} [Nonempty C]
    (fuel inlineLimit cutSize : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig nextSource : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (declarations : List AstHOL.Dec) (expressions : List ClosLang.Exp)
    (config current output : ClosToBvl.Config) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs
      (sourceClosureCompiler config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler))
    (sourceRun : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextSource, expressions))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (closureRun : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel fuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel fuel fuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel fuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel fuel afterTmc = some (bviCache, final))
    (numberSafe : ¬ ClosProps.containsAppSome config.maxApp expressions) (varsSafe : ClosProps.everyFnVarsNone expressions)
    (oracleSafe : ∀ i, ((sourceClosureOracle flatConfig) i).2.2 = [] ∧
      ¬ ClosProps.containsAppSome config.maxApp ((sourceClosureOracle flatConfig) i).2.1 ∧
        ClosProps.everyFnVarsNone ((sourceClosureOracle flatConfig) i).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) (sourceClosureOracle flatConfig))
    (initialBound : current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : tailLast ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = bviCache) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (BviSem.semantics source.ffi (sptFromAList final)
        (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
          (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
            (BvlInline.Proofs.letOpOracle splitSeq cutSize
              (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit
                (closureFuture config.maxApp (sourceClosureOracle flatConfig)))))))) compiler targetStart) := by
  have sourceBehavior := cakeCompileToClosFuel_semantics_exists fuel interp source sourceEnv sourceConfig nextSource
    flatConfig (sourceClosureCompiler config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)
    declarations expressions config.maxApp precondition safe positive production sourceRun
  have nonfail : ClosSem.semantics source.ffi config.maxApp HolFiniteMapExact.empty (sourceClosureOracle flatConfig)
      (sourceClosureCompiler config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler) expressions ≠ .fail := by
    intro failure
    rw [failure] at sourceBehavior
    exact safe sourceBehavior
  have backend := noOpts_closure_optimized_bvi_semantics source.ffi fuel fuel inlineLimit cutSize fuel fuel
    splitSeq tailEnabled tmcEnabled config current output expressions program compiled names (sourceClosureOracle flatConfig)
    compiler cache optimized targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache
    mti calls known preprocess closureRun optimizedRun lowerRun tailRun tmcRun inlineRun nonfail numberSafe varsSafe
    oracleSafe oracleState initialBound cacheEq oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker
    lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  rw [backend]
  exact sourceBehavior

/-- A successful configured driver returns the code and entry point covered by the
source-to-BVI behavior composition. -/
theorem cakeConfiguredToBvi_semantics_proofSide {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig nextSource : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (declarations : List AstHOL.Dec) (expressions : List ClosLang.Exp)
    (config current output : ClosToBvl.Config) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (resultCode : List (Nat × Nat × Bvi.Exp)) (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultCode, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs
      (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiler))
    (sourceRun : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextSource, expressions))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (closureRun : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel fuel bvlConfig.inlineSizeLimit bvlConfig.expCut bvlConfig.splitMainAtSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel fuel fuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel fuel bvlConfig.doTailrec (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel bvlConfig.doTmc (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel fuel afterTmc = some (bviCache, final))
    (numberSafe : ¬ ClosProps.containsAppSome config.maxApp expressions) (varsSafe : ClosProps.everyFnVarsNone expressions)
    (oracleSafe : ∀ i, ((sourceClosureOracle flatConfig) i).2.2 = [] ∧
      ¬ ClosProps.containsAppSome config.maxApp ((sourceClosureOracle flatConfig) i).2.1 ∧
        ClosProps.everyFnVarsNone ((sourceClosureOracle flatConfig) i).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) (sourceClosureOracle flatConfig))
    (initialBound : current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : tailLast ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = bviCache) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (BviSem.semantics source.ffi (sptFromAList resultCode)
        (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource bvlConfig.doTmc)
          (stateCo (BviTailrec.compileProgSource bvlConfig.doTailrec) (stateCo BvlToBvi.compileIncSource
            (BvlInline.Proofs.letOpOracle bvlConfig.splitMainAtSeq bvlConfig.expCut
              (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo bvlConfig.inlineSizeLimit
                (closureFuture config.maxApp (sourceClosureOracle flatConfig)))))))) compiler resultClosure.start) := by
  have behavior := cakeToOptimizedBvi_semantics_proofSide fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
    bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc interp source sourceEnv sourceConfig nextSource
    flatConfig compiler declarations expressions config current output program compiled names cache optimized targetStart targetNext
    lowered beforeTmc afterTmc final tailLast tmcLast bviCache precondition safe positive production sourceRun mti calls known
    preprocess closureRun optimizedRun lowerRun tailRun tmcRun inlineRun numberSafe varsSafe oracleSafe oracleState initialBound
    cacheEq oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  simp [SourceToFlat.compileCakeToBviConfiguredFuel, sourceRun, closureRun, optimizedRun, lowerRun, tailRun, tmcRun, inlineRun] at run
  obtain ⟨_, closureEq, _, codeEq, _⟩ := run
  subst resultCode
  rw [← closureEq]
  exact behavior

end Flapjack.Compiler.Backend.FlatToClos
