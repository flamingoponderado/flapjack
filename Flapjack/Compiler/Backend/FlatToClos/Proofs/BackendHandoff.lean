import Flapjack.Compiler.Backend.FlatToClos.Proofs.SourcePreprocessing
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.LoweringHandoff
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Syntactic
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BviStages
import Flapjack.Compiler.Backend.BviToData.Proofs.Semantics
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordStages
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberAndAnnotate

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

/-- A successful configured source-to-BVI run contains a source-to-closure
execution whose behavior is an observable source behavior. This composition
still assumes the source precondition and compiler callback relation. -/
theorem configuredSourceClosure_semantics {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (resultCode : List (Nat × Nat × Bvi.Exp)) (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultCode, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs
      (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
        bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiler)) :
    ∃ expressions,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) ∧
      Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
        (ClosSem.semantics source.ffi config.maxApp HolFiniteMapExact.empty
          (sourceClosureOracle flatConfig)
          (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
            bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiler) expressions) := by
  obtain ⟨source', expressions, _, _, _, _, _, _, _, _, _, _, _, _, _, sourceRun,
    _, _, _, _, _, _, sourceEq, _⟩ :=
    SourceToFlat.configured_bvi_all_stage_witnesses fuel sourceConfig config bvlConfig declarations
      resultSource resultClosure resultConfig resultCode resultNames run
  subst source'
  exact ⟨expressions, sourceRun,
    cakeCompileToClosFuel_semantics_exists fuel interp source sourceEnv sourceConfig resultSource
      flatConfig _ declarations expressions config.maxApp precondition safe positive production sourceRun⟩

/-- Successful source-to-closure compilation supplies the syntactic invariants
required by closure numbering and annotation. -/
theorem sourceClosure_syntactic (fuel maxApp : Nat) (positive : 0 < maxApp)
    (sourceConfig nextSource : SourceToFlat.Config) (declarations : List AstHOL.Dec)
    (expressions : List ClosLang.Exp)
    (run : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextSource, expressions)) :
    ¬ ClosProps.containsAppSome maxApp expressions ∧ ClosProps.everyFnVarsNone expressions := by
  have output := congrArg (Option.map Prod.snd) run
  have same : compileProg (SourceToFlat.compileTotal sourceConfig (SourceToSource.compile declarations)).2 = expressions := by
    apply Option.some.inj
    simpa [SourceToFlat.compileCakeToClosFuel, SourceToFlat.compileToClosFuel, SourceToFlat.compile] using output
  rw [← same]
  have properties := compileProg_syntacticProps maxApp
    (SourceToFlat.compileTotal sourceConfig (SourceToSource.compile declarations)).2
  exact ⟨properties.2.2 positive, properties.2.1⟩

/-- Each incremental closure compilation supplies the same invariants and
does not introduce an auxiliary code list. -/
theorem sourceClosureOracle_syntactic {C : Type} (config : FlatSem.InstallConfig C)
    (maxApp : Nat) (positive : 0 < maxApp) (i : Nat) :
    ((sourceClosureOracle config) i).2.2 = [] ∧
      ¬ ClosProps.containsAppSome maxApp ((sourceClosureOracle config) i).2.1 ∧
        ClosProps.everyFnVarsNone ((sourceClosureOracle config) i).2.1 := by
  cases h : config.compileOracle i with
  | mk state declarations =>
    have props := incCompileDecs_syntacticProps (α := C) (β := C) (γ := C) maxApp declarations
    refine ⟨?_, ?_, ?_⟩
    · simp [sourceClosureOracle, pureCo, h, incCompileDecs]
    · simpa [sourceClosureOracle, Function.comp_def, pureCo, h, incCompileDecs] using props.2.2 positive
    · simpa [sourceClosureOracle, Function.comp_def, pureCo, h, incCompileDecs] using props.2.1

/-- Source compilation followed by the executed multi-argument pass,
numbering and annotation has an observable source behavior. The source-pass
precondition and callback relation remain assumptions, and the participating
semantics have not yet been reviewed as a HOL correspondence. -/
theorem cakeToAnnotatedMti_semantics_proofSide {C F : Type} [Nonempty C]
    (fuel maxApp number : Nat)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig nextSource : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × C)) (compiler : ClosSem.Compiler C)
    (declarations : List AstHOL.Dec) (expressions : List ClosLang.Exp)
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp)
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (pureCc (ClosMti.compileInc (Input := List (Nat × Nat × ClosLang.Exp)) maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler))))
    (sourceRun : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextSource, expressions)) :
    ∃ transformed, ClosMti.compileFuel fuel true maxApp expressions = some transformed ∧
      Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
        (ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
          (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
            (pureCo (ClosMti.compileInc maxApp) ∘ sourceClosureOracle flatConfig)) compiler
          (ClosAnnotate.annotateList 0 (ClosNumber.renumberList number transformed).2)) := by
  let intermediate : ClosSem.Compiler (Nat × C) := pureCc (ClosMti.compileInc maxApp)
    (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler))
  have sourceBehavior := cakeCompileToClosFuel_semantics_exists fuel interp source sourceEnv sourceConfig
    nextSource flatConfig intermediate declarations expressions maxApp precondition safe positive production sourceRun
  have nonfail : ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
      (sourceClosureOracle flatConfig) intermediate expressions ≠ .fail := by
    intro failure
    rw [failure] at sourceBehavior
    exact safe sourceBehavior
  have unary : ∀ e ∈ expressions, ClosProps.noMti e := by
    have output := congrArg (Option.map Prod.snd) sourceRun
    have same : compileProg (SourceToFlat.compileTotal sourceConfig (SourceToSource.compile declarations)).2 = expressions := by
      apply Option.some.inj
      simpa [SourceToFlat.compileCakeToClosFuel, SourceToFlat.compileToClosFuel, SourceToFlat.compile] using output
    rw [← same]
    exact compileProg_noMti _
  have oracleUnary : ∀ index, ((sourceClosureOracle flatConfig) index).2.2 = [] ∧
      ∀ e ∈ ((sourceClosureOracle flatConfig) index).2.1, ClosProps.noMti e := by
    intro index
    change (incCompileDecs (flatConfig.compileOracle index).2).2 = [] ∧
      ∀ e ∈ (incCompileDecs (flatConfig.compileOracle index).2).1, ClosProps.noMti e
    exact ⟨rfl, incCompileDecs_noMti _⟩
  obtain ⟨transformed, compiled, behavior⟩ := compileFuel_number_annotate_semantics
    source.ffi fuel maxApp number (sourceClosureOracle flatConfig) compiler expressions
    positive unary oracleUnary nonfail
  refine ⟨transformed, compiled, ?_⟩
  rw [behavior]
  exact sourceBehavior

/-- Source-to-BVI behavior composition with multi-argument introduction
enabled. Source-pass, callback, incremental-oracle, cache and counter
conditions remain explicit; this is not a reviewed end-to-end HOL theorem. -/
theorem cakeToOptimizedBviMti_semantics_proofSide {C F : Type} [Nonempty C]
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
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (pureCc (ClosMti.compileInc (Input := List (Nat × Nat × ClosLang.Exp)) config.maxApp)
        (sourceClosureCompiler config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))
    (sourceRun : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextSource, expressions))
    (enabled : config.doMti = true) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? { config with doMti := false }
      (ClosMti.introList config.maxApp expressions) = some (current, program))
    (closureRun : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel fuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel fuel fuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel fuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel fuel afterTmc = some (bviCache, final))
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ sourceClosureOracle flatConfig))
    (initialBound : current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : tailLast ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = bviCache) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (BviSem.semantics source.ffi (sptFromAList final)
        (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
          (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
            (BvlInline.Proofs.letOpOracle splitSeq cutSize
              (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit
                (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig)))))))) compiler targetStart) := by
  let intermediate : ClosSem.Compiler (Nat × OptimizationConfig C) := pureCc (ClosMti.compileInc config.maxApp)
    (sourceClosureCompiler config.maxApp inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)
  have sourceBehavior := cakeCompileToClosFuel_semantics_exists fuel interp source sourceEnv sourceConfig nextSource
    flatConfig intermediate declarations expressions config.maxApp precondition safe positive production sourceRun
  have nonfail : ClosSem.semantics source.ffi config.maxApp HolFiniteMapExact.empty (sourceClosureOracle flatConfig)
      intermediate expressions ≠ .fail := by
    intro failure
    rw [failure] at sourceBehavior
    exact safe sourceBehavior
  have unary : ∀ e ∈ expressions, ClosProps.noMti e := by
    have output := congrArg (Option.map Prod.snd) sourceRun
    have same : compileProg (SourceToFlat.compileTotal sourceConfig (SourceToSource.compile declarations)).2 = expressions := by
      apply Option.some.inj
      simpa [SourceToFlat.compileCakeToClosFuel, SourceToFlat.compileToClosFuel, SourceToFlat.compile] using output
    rw [← same]
    exact compileProg_noMti _
  have oracleUnary : ∀ index, ((sourceClosureOracle flatConfig) index).2.2 = [] ∧
      ∀ e ∈ ((sourceClosureOracle flatConfig) index).2.1, ClosProps.noMti e := by
    intro index
    change (incCompileDecs (flatConfig.compileOracle index).2).2 = [] ∧
      ∀ e ∈ (incCompileDecs (flatConfig.compileOracle index).2).1, ClosProps.noMti e
    exact ⟨rfl, incCompileDecs_noMti _⟩
  have backend := mti_closure_optimized_bvi_semantics source.ffi fuel fuel inlineLimit cutSize fuel fuel
    splitSeq tailEnabled tmcEnabled config current output expressions program compiled names (sourceClosureOracle flatConfig)
    compiler cache optimized targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache
    enabled calls known positive unary oracleUnary preprocess closureRun optimizedRun lowerRun tailRun tmcRun inlineRun
    nonfail oracleState initialBound cacheEq oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker
    lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  rw [backend]
  exact sourceBehavior

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
  have ⟨numberSafe, varsSafe⟩ := sourceClosure_syntactic fuel config.maxApp positive
    sourceConfig nextSource declarations expressions sourceRun
  have oracleSafe := sourceClosureOracle_syntactic flatConfig config.maxApp positive
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
    preprocess closureRun optimizedRun lowerRun tailRun tmcRun inlineRun oracleState initialBound
    cacheEq oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq
  simp [SourceToFlat.compileCakeToBviConfiguredFuel, sourceRun, closureRun, optimizedRun, lowerRun, tailRun, tmcRun, inlineRun] at run
  obtain ⟨_, closureEq, _, codeEq, _⟩ := run
  subst resultCode
  rw [← closureEq]
  exact behavior

/-- Conditional source-to-BVI behavior for the actual configured execution.
Intermediate successful runs and caches are recovered from `run`; the
remaining bounds and oracle relations are explicit proof obligations. -/
theorem cakeConfiguredToBvi_semantics_from_run {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (resultCode : List (Nat × Nat × Bvi.Exp)) (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultCode, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs
      (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
        bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiler))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) (sourceClosureOracle flatConfig))
    (initialBound : ∀ expressions current program,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) →
      compileCommonNoOpts? config expressions = some (current, program) →
      current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = resultConfig.inlines)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : resultConfig.nextName1 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : resultConfig.nextName2 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : resultConfig.nextName3 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = resultConfig.bviInlines) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (BviSem.semantics source.ffi (sptFromAList resultCode)
        (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource bvlConfig.doTmc)
          (stateCo (BviTailrec.compileProgSource bvlConfig.doTailrec) (stateCo BvlToBvi.compileIncSource
            (BvlInline.Proofs.letOpOracle bvlConfig.splitMainAtSeq bvlConfig.expCut
              (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo bvlConfig.inlineSizeLimit
                (closureFuture config.maxApp (sourceClosureOracle flatConfig)))))))) compiler resultClosure.start) := by
  obtain ⟨source', expressions, output, compiled, names, cache, optimized, targetStart, lowered,
    targetNext, tailLast, beforeTmc, tmcLast, afterTmc, bviCache, sourceRun, closureRun,
    optimizedRun, lowerRun, tailRun, tmcRun, inlineRun, sourceEq, closureEq, configEq, _⟩ :=
    SourceToFlat.configured_bvi_all_stage_witnesses fuel sourceConfig config bvlConfig declarations
      resultSource resultClosure resultConfig resultCode resultNames run
  subst resultSource
  subst resultClosure
  subst resultConfig
  cases preprocess : compileCommonNoOpts? config expressions with
  | none => simp [compileCommonNoOpts?, mti, calls, known] at preprocess
  | some pair =>
    obtain ⟨current, program⟩ := pair
    have bound := initialBound expressions current program sourceRun preprocess
    exact cakeToOptimizedBvi_semantics_proofSide fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
      bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc interp source sourceEnv sourceConfig source'
      flatConfig compiler declarations expressions config current output program compiled names cache optimized targetStart targetNext
      lowered beforeTmc afterTmc resultCode tailLast tmcLast bviCache precondition safe positive production sourceRun mti calls known
      preprocess closureRun optimizedRun lowerRun tailRun tmcRun inlineRun oracleState bound
      cacheEq oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq

/-- Conditional source-to-BVI behavior for the configured execution with
multi-argument introduction enabled.
Intermediate successful runs and caches are recovered from `run`; the
remaining bounds and oracle relations are explicit proof obligations. -/
theorem cakeConfiguredToBviMti_semantics_from_run {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (resultCode : List (Nat × Nat × Bvi.Exp)) (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultCode, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (pureCc (ClosMti.compileInc (Input := List (Nat × Nat × ClosLang.Exp)) config.maxApp)
        (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
          bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiler)))
    (enabled : config.doMti = true) (calls : config.doCall = false) (known : config.knownConf = none)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ sourceClosureOracle flatConfig))
    (initialBound : ∀ expressions current program,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) →
      compileCommonNoOpts? { config with doMti := false } (ClosMti.introList config.maxApp expressions) = some (current, program) →
      current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = resultConfig.inlines)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : resultConfig.nextName1 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : resultConfig.nextName2 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : resultConfig.nextName3 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = resultConfig.bviInlines) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (BviSem.semantics source.ffi (sptFromAList resultCode)
        (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource bvlConfig.doTmc)
          (stateCo (BviTailrec.compileProgSource bvlConfig.doTailrec) (stateCo BvlToBvi.compileIncSource
            (BvlInline.Proofs.letOpOracle bvlConfig.splitMainAtSeq bvlConfig.expCut
              (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo bvlConfig.inlineSizeLimit
                (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig)))))))) compiler resultClosure.start) := by
  obtain ⟨source', expressions, output, compiled, names, cache, optimized, targetStart, lowered,
    targetNext, tailLast, beforeTmc, tmcLast, afterTmc, bviCache, sourceRun, closureRun,
    optimizedRun, lowerRun, tailRun, tmcRun, inlineRun, sourceEq, closureEq, configEq, _⟩ :=
    SourceToFlat.configured_bvi_all_stage_witnesses fuel sourceConfig config bvlConfig declarations
      resultSource resultClosure resultConfig resultCode resultNames run
  subst resultSource
  subst resultClosure
  subst resultConfig
  cases preprocess : compileCommonNoOpts? { config with doMti := false } (ClosMti.introList config.maxApp expressions) with
  | none => simp [compileCommonNoOpts?, calls, known] at preprocess
  | some pair =>
    obtain ⟨current, program⟩ := pair
    have bound := initialBound expressions current program sourceRun preprocess
    exact cakeToOptimizedBviMti_semantics_proofSide fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
      bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc interp source sourceEnv sourceConfig source'
      flatConfig compiler declarations expressions config current output program compiled names cache optimized targetStart targetNext
      lowered beforeTmc afterTmc resultCode tailLast tmcLast bviCache precondition safe positive production sourceRun enabled calls known
      preprocess closureRun optimizedRun lowerRun tailRun tmcRun inlineRun oracleState bound
      cacheEq oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq

/-- The BVI oracle used by the configured source-to-BVI correctness chain. -/
noncomputable abbrev configuredBviOracle {C : Type} (maxApp : Nat) (config : BvlToBvi.Config)
    (oracle : ClosSem.CompileOracle (Nat × OptimizationConfig C)) : BviSem.CompileOracle C :=
  stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource config.doTmc)
    (stateCo (BviTailrec.compileProgSource config.doTailrec) (stateCo BvlToBvi.compileIncSource
      (BvlInline.Proofs.letOpOracle config.splitMainAtSeq config.expCut
        (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo config.inlineSizeLimit
          (closureFuture maxApp oracle))))))

/-- The BVI oracle after enabled incremental multi-argument introduction. -/
noncomputable abbrev configuredMtiBviOracle {C : Type} (maxApp : Nat) (config : BvlToBvi.Config)
    (oracle : ClosSem.CompileOracle (Nat × OptimizationConfig C)) : BviSem.CompileOracle C :=
  stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource config.doTmc)
    (stateCo (BviTailrec.compileProgSource config.doTailrec) (stateCo BvlToBvi.compileIncSource
      (BvlInline.Proofs.letOpOracle config.splitMainAtSeq config.expCut
        (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo config.inlineSizeLimit
          (mtiClosureFuture maxApp oracle))))))

/-- Compose the configured source-to-BVI behavior with BVI-to-data simulation,
and identify the executed bounded data compilation with the simulated code.
The source, oracle, cache, and disabled-optimization assumptions remain explicit;
HOL correspondence of the BVI and data semantics remains under review. -/
theorem cakeConfiguredToData_semantics_from_run {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (resultCode : List (Nat × Nat × Bvi.Exp)) (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultCode, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs
      (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
        bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc
        (fun cfg code => compiler cfg (BviToData.compileProg code))))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) (sourceClosureOracle flatConfig))
    (initialBound : ∀ expressions current program,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) →
      compileCommonNoOpts? config expressions = some (current, program) →
      current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = resultConfig.inlines)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : resultConfig.nextName1 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : resultConfig.nextName2 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : resultConfig.nextName3 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = resultConfig.bviInlines) :
    let oracle := configuredBviOracle config.maxApp bvlConfig (sourceClosureOracle flatConfig)
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (DataSem.semantics source.ffi (sptFromAList (BviToData.compileProg resultCode))
        (fun n => let (cfg, code) := oracle n; (cfg, BviToData.compileProg code))
        compiler limits sizes resultClosure.start) ∧
      (resultCode.mapM fun (name, argc, body) => do
        pure (name, argc, ← BviToData.compileExpBounded fuel argc body)) =
        some (BviToData.compileProg resultCode) := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let oracle := configuredBviOracle config.maxApp bvlConfig (sourceClosureOracle flatConfig)
  have behavior := cakeConfiguredToBvi_semantics_from_run fuel bvlConfig interp source sourceEnv sourceConfig
    flatConfig bviCompiler declarations config resultSource resultClosure resultConfig resultCode resultNames
    run precondition safe positive production mti calls known oracleState initialBound cacheEq
    oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound
    tmcCounterBound bviCacheEq
  have noFail : BviSem.semantics source.ffi (sptFromAList resultCode) oracle bviCompiler resultClosure.start ≠ .fail := by
    intro failure
    apply safe
    simpa [oracle, configuredBviOracle, bviCompiler, failure] using behavior
  have agreement := BviToData.compileProg_semantics source.ffi resultCode oracle compiler limits sizes resultClosure.start noFail
  dsimp only
  constructor
  · rw [agreement]
    exact behavior
  · exact BviToData.compileProgBounded_agrees fuel resultCode

/-- Compose the enabled multi-argument source-to-BVI path with BVI-to-data simulation,
and identify the executed bounded data compilation with the simulated code.
The source, oracle and cache assumptions remain explicit; known-function and
direct-call conversion are disabled. HOL correspondence of the BVI and data
semantics remains under review. -/
theorem cakeConfiguredToDataMti_semantics_from_run {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (resultCode : List (Nat × Nat × Bvi.Exp)) (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultCode, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (pureCc (ClosMti.compileInc (Input := List (Nat × Nat × ClosLang.Exp)) config.maxApp)
        (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
          bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc
          (fun cfg code => compiler cfg (BviToData.compileProg code)))))
    (enabled : config.doMti = true) (calls : config.doCall = false) (known : config.knownConf = none)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ sourceClosureOracle flatConfig))
    (initialBound : ∀ expressions current program,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) →
      compileCommonNoOpts? { config with doMti := false } (ClosMti.introList config.maxApp expressions) = some (current, program) →
      current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = resultConfig.inlines)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : resultConfig.nextName1 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : resultConfig.nextName2 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : resultConfig.nextName3 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = resultConfig.bviInlines) :
    let oracle := configuredMtiBviOracle config.maxApp bvlConfig (sourceClosureOracle flatConfig)
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (DataSem.semantics source.ffi (sptFromAList (BviToData.compileProg resultCode))
        (fun n => let (cfg, code) := oracle n; (cfg, BviToData.compileProg code))
        compiler limits sizes resultClosure.start) ∧
      (resultCode.mapM fun (name, argc, body) => do
        pure (name, argc, ← BviToData.compileExpBounded fuel argc body)) =
        some (BviToData.compileProg resultCode) := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let oracle := configuredMtiBviOracle config.maxApp bvlConfig (sourceClosureOracle flatConfig)
  have behavior := cakeConfiguredToBviMti_semantics_from_run fuel bvlConfig interp source sourceEnv sourceConfig
    flatConfig bviCompiler declarations config resultSource resultClosure resultConfig resultCode resultNames
    run precondition safe positive production enabled calls known oracleState initialBound cacheEq
    oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound
    tmcCounterBound bviCacheEq
  have noFail : BviSem.semantics source.ffi (sptFromAList resultCode) oracle bviCompiler resultClosure.start ≠ .fail := by
    intro failure
    apply safe
    simpa [oracle, configuredMtiBviOracle, bviCompiler, failure] using behavior
  have agreement := BviToData.compileProg_semantics source.ffi resultCode oracle compiler limits sizes resultClosure.start noFail
  dsimp only
  constructor
  · rw [agreement]
    exact behavior
  · exact BviToData.compileProgBounded_agrees fuel resultCode

/-- The data program simulated by the source-to-data proof is the one fed to
checked word lowering in a successful configured source-to-word execution.
This leaves data-to-word semantic preservation as a separate obligation. -/
theorem cakeConfiguredWordRun_data_behavior {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (wordConfig : DataToWord.Config) (resultWord : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToWord64ConfiguredFuel fuel sourceConfig config bvlConfig wordConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultWord, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs
      (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
        bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc
        (fun cfg code => compiler cfg (BviToData.compileProg code))))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) (sourceClosureOracle flatConfig))
    (initialBound : ∀ expressions current program,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) →
      compileCommonNoOpts? config expressions = some (current, program) →
      current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = resultConfig.inlines)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (closureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : resultConfig.nextName1 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : resultConfig.nextName2 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : resultConfig.nextName3 ≤ (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (closureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = resultConfig.bviInlines) :
    let oracle := configuredBviOracle config.maxApp bvlConfig (sourceClosureOracle flatConfig)
    ∃ bviCode lowered fixed bignum,
      SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
        some (resultSource, resultClosure, resultConfig, bviCode, resultNames) ∧
      ((BviToData.compileProg bviCode).mapM fun (name, args, body) => do
        let (body, _) ← DataToWord.compileControl? (width := 64) wordConfig name 2 body
        pure (name, args + 1, body)) = some lowered ∧
      DataToWord.fixedStubs? wordConfig = some fixed ∧
      WordBignum.generateStubs 64 DataToWord.bignumLocation = some bignum ∧
      resultWord = fixed ++ bignum ++ lowered ∧
      Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
        (DataSem.semantics source.ffi (sptFromAList (BviToData.compileProg bviCode))
          (fun n => let (cfg, code) := oracle n; (cfg, BviToData.compileProg code))
          compiler limits sizes resultClosure.start) := by
  obtain ⟨bviCode, lowered, fixed, bignum, bviRun, lowerRun, fixedRun, bignumRun, outputEq⟩ :=
    SourceToFlat.configured_word_stage_witnesses fuel sourceConfig config bvlConfig wordConfig declarations
      resultSource resultClosure resultConfig resultWord resultNames run
  have behavior := cakeConfiguredToData_semantics_from_run fuel bvlConfig interp source sourceEnv sourceConfig
    flatConfig compiler limits sizes declarations config resultSource resultClosure resultConfig bviCode resultNames
    bviRun precondition safe positive production mti calls known oracleState initialBound cacheEq
    oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound
    tmcCounterBound bviCacheEq
  exact ⟨bviCode, lowered, fixed, bignum, bviRun, lowerRun, fixedRun, bignumRun, outputEq, behavior.1⟩

/-- With multi-argument introduction enabled, the data program simulated by the
source-to-data proof is the one fed to
checked word lowering in a successful configured source-to-word execution.
This leaves data-to-word semantic preservation as a separate obligation. -/
theorem cakeConfiguredWordMtiRun_data_behavior {C F : Type} [Nonempty C]
    (fuel : Nat) (bvlConfig : BvlToBvi.Config)
    (interp : Option (Value → Option (SourceToFlat.Config × (Nat × OptimizationConfig C))))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig (Nat × OptimizationConfig C)) (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (declarations : List AstHOL.Dec) (config : ClosToBvl.Config)
    (resultSource : SourceToFlat.Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (wordConfig : DataToWord.Config) (resultWord : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (resultNames : Spt Basis.Pure.MlString.MlString)
    (run : SourceToFlat.compileCakeToWord64ConfiguredFuel fuel sourceConfig config bvlConfig wordConfig declarations =
      some (resultSource, resultClosure, resultConfig, resultWord, resultNames))
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < config.maxApp)
    (production : flatConfig.compile = pureCc (incCompileDecs (α := Nat × Nat × ClosLang.Exp))
      (pureCc (ClosMti.compileInc (Input := List (Nat × Nat × ClosLang.Exp)) config.maxApp)
        (sourceClosureCompiler config.maxApp bvlConfig.inlineSizeLimit bvlConfig.expCut
          bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc
          (fun cfg code => compiler cfg (BviToData.compileProg code)))))
    (enabled : config.doMti = true) (calls : config.doCall = false) (known : config.knownConf = none)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ sourceClosureOracle flatConfig))
    (initialBound : ∀ expressions current program,
      SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (resultSource, expressions) →
      compileCommonNoOpts? { config with doMti := false } (ClosMti.introList config.maxApp expressions) = some (current, program) →
      current.nextLoc ≤ ((sourceClosureOracle flatConfig) 0).1.1)
    (cacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.1 = resultConfig.inlines)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) i).1.2.2.2.1)
    (lowerCounterBound : resultConfig.nextName1 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.1)
    (tailCounterBound : resultConfig.nextName2 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.1)
    (tmcCounterBound : resultConfig.nextName3 ≤ (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.1)
    (bviCacheEq : (mtiClosureFuture config.maxApp (sourceClosureOracle flatConfig) 0).1.2.2.2.2.1 = resultConfig.bviInlines) :
    let oracle := configuredMtiBviOracle config.maxApp bvlConfig (sourceClosureOracle flatConfig)
    ∃ bviCode lowered fixed bignum,
      SourceToFlat.compileCakeToBviConfiguredFuel fuel sourceConfig config bvlConfig declarations =
        some (resultSource, resultClosure, resultConfig, bviCode, resultNames) ∧
      ((BviToData.compileProg bviCode).mapM fun (name, args, body) => do
        let (body, _) ← DataToWord.compileControl? (width := 64) wordConfig name 2 body
        pure (name, args + 1, body)) = some lowered ∧
      DataToWord.fixedStubs? wordConfig = some fixed ∧
      WordBignum.generateStubs 64 DataToWord.bignumLocation = some bignum ∧
      resultWord = fixed ++ bignum ++ lowered ∧
      Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
        (DataSem.semantics source.ffi (sptFromAList (BviToData.compileProg bviCode))
          (fun n => let (cfg, code) := oracle n; (cfg, BviToData.compileProg code))
          compiler limits sizes resultClosure.start) := by
  obtain ⟨bviCode, lowered, fixed, bignum, bviRun, lowerRun, fixedRun, bignumRun, outputEq⟩ :=
    SourceToFlat.configured_word_stage_witnesses fuel sourceConfig config bvlConfig wordConfig declarations
      resultSource resultClosure resultConfig resultWord resultNames run
  have behavior := cakeConfiguredToDataMti_semantics_from_run fuel bvlConfig interp source sourceEnv sourceConfig
    flatConfig compiler limits sizes declarations config resultSource resultClosure resultConfig bviCode resultNames
    bviRun precondition safe positive production enabled calls known oracleState initialBound cacheEq
    oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound
    tmcCounterBound bviCacheEq
  exact ⟨bviCode, lowered, fixed, bignum, bviRun, lowerRun, fixedRun, bignumRun, outputEq, behavior.1⟩

end Flapjack.Compiler.Backend.FlatToClos
