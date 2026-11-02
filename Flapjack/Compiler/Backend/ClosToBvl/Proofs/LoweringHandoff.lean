import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationCodeSemantics
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InlineHandoff

/-! Behavior composition from unoptimized closure conversion through BVI lowering. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- The production closure driver with optional closure optimizations disabled,
followed by checked BVL-to-BVI lowering, preserves proof-side source behavior.
The source safety, handler and oracle conditions remain explicit; this is not a
reviewed HOL theorem or a full CakeML-to-target correctness statement. -/
theorem noOpts_closure_lowering_semantics {C F : Type} (ffi : HolFfiState F)
    (closureFuel lowerFuel optFuel : Nat) (config current output : Config)
    (expressions : List ClosLang.Exp) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × (Nat × C))) (compiler : BviSem.Compiler C)
    (targetStart targetNext : Nat) (lowered : List (Nat × Nat × Bvi.Exp))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (lowerRun : BvlToBvi.compileProgFuel lowerFuel optFuel output.start 0 compiled =
      some (targetStart, lowered, targetNext))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
          (stateCc BvlToBvi.compileIncSource compiler)))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions) (varsSafe : everyFnVarsNone expressions)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : current.nextLoc ≤ (oracle 0).1.1)
    (handlers : BvlHandle.Proofs.handleOk (compiled.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk
      (((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNext ≤ ((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
      stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) 0).1.1) :
    BviSem.semantics ffi (sptFromAList lowered)
      (stateCo BvlToBvi.compileIncSource (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)) compiler targetStart =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
            (stateCc BvlToBvi.compileIncSource compiler)))) expressions := by
  let bvlOracle := pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
    stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  have closureEq := compileCallMtiFuel_noOpts_semantics ffi closureFuel config current output expressions
    program compiled names oracle (stateCc BvlToBvi.compileIncSource compiler) mti calls known preprocess closureRun
    nonfail numberSafe varsSafe oracleSafe oracleState initialBound
  have bvlNonfail : BvlSem.semantics ffi (sptFromAList compiled) bvlOracle
      (stateCc BvlToBvi.compileIncSource compiler) output.start ≠ .fail := by
    rw [closureEq]
    exact nonfail
  have noOptsRun : compileNoOpts? config expressions = some (output, compiled, names) := by
    simpa [← compileCallMtiFuel_noOpts closureFuel config expressions mti calls known] using closureRun
  have distinct := compileNoOpts_prepared_labels_nodup config current output expressions program compiled names
    preprocess noOptsRun
  have loweredEq := BvlToBvi.Proofs.compileProgFuel_semantics lowerFuel optFuel output.start 0 ffi
    compiled bvlOracle compiler targetStart targetNext lowered lowerRun distinct handlers oracleHandlers counterBound bvlNonfail
  exact loweredEq.trans closureEq

/-- Configuration carried through BVL optimization and successive BVI passes. -/
abbrev OptimizationConfig (C : Type) :=
  Spt (Nat × Bvl.Exp) × (Nat × (Nat × (Nat × (Spt (Nat × Bvi.Exp) × C))))

/-- BVL compiler callback for the implemented optimization and lowering stages. -/
noncomputable abbrev optimizationCallback {C : Type} (inlineLimit cutSize : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (compiler : BviSem.Compiler C) : BvlSem.Compiler (OptimizationConfig C) :=
  BvlInline.Proofs.inCc inlineLimit (BvlInline.Proofs.removeTicksCc
    (BvlInline.Proofs.letOpCompiler splitSeq cutSize
      (stateCc BvlToBvi.compileIncSource (stateCc (BviTailrec.compileProgSource tailEnabled)
        (stateCc (BviTmc.compileProgSource tmcEnabled) (stateCc BviInline.compileIncSource compiler))))))

/-- Numbering, annotation and closure conversion applied to a future oracle. -/
noncomputable abbrev closureFuture {C : Type} (maxApp : Nat) (oracle : ClosSem.CompileOracle (Nat × C)) : BvlSem.CompileOracle C :=
  pureCo (compileInc maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
    stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle

/-- Closure conversion with optional closure optimizations disabled, followed
by BVL optimization, lowering, BVI tail recursion, TMC and inlining, preserves
non-failing source behavior under the stated cache, oracle and counter
conditions. The underlying evaluator correspondence remains under review. -/
theorem noOpts_closure_optimized_bvi_semantics {C F : Type} (ffi : HolFfiState F)
    (closureFuel bvlFuel inlineLimit cutSize bviFuel optFuel : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel bviFuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, final))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc
        (pureCc (compileInc config.maxApp) (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions) (varsSafe : everyFnVarsNone expressions)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : current.nextLoc ≤ (oracle 0).1.1)
    (cacheEq : (closureFuture config.maxApp oracle 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ ((closureFuture config.maxApp oracle) i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace ((closureFuture config.maxApp oracle) i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ ((closureFuture config.maxApp oracle) i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace ((closureFuture config.maxApp oracle) i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ (closureFuture config.maxApp oracle 0).1.2.1)
    (tailCounterBound : tailLast ≤ (closureFuture config.maxApp oracle 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (closureFuture config.maxApp oracle 0).1.2.2.2.1)
    (bviCacheEq : (closureFuture config.maxApp oracle 0).1.2.2.2.2.1 = bviCache) :
    BviSem.semantics ffi (sptFromAList final)
      (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
        (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
          (BvlInline.Proofs.letOpOracle splitSeq cutSize
            (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit (closureFuture config.maxApp oracle)))))))
      compiler targetStart =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)))) expressions := by
  have closureEq := compileCallMtiFuel_noOpts_semantics ffi closureFuel config current output expressions
    program compiled names oracle (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)
    mti calls known preprocess closureRun nonfail numberSafe varsSafe oracleSafe oracleState initialBound
  have bvlNonfail : BvlSem.semantics ffi (sptFromAList compiled) (closureFuture config.maxApp oracle)
      (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler) output.start ≠ .fail := by
    rw [closureEq]
    exact nonfail
  have noOptsRun : compileNoOpts? config expressions = some (output, compiled, names) := by
    simpa [← compileCallMtiFuel_noOpts closureFuel config expressions mti calls known] using closureRun
  have distinct := compileNoOpts_prepared_labels_nodup config current output expressions program compiled names preprocess noOptsRun
  have oracleDistinct : ∀ i, (((closureFuture config.maxApp oracle) i).2.map Prod.fst).Nodup := by
    exact numberedAnnotatedOracle_labels_nodup_emptyAux config.maxApp oracle (fun i => (oracleSafe i).1)
  have optimizedEq := BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_semantics bvlFuel inlineLimit cutSize bviFuel optFuel
    output.start 0 splitSeq tailEnabled tmcEnabled ffi compiled (closureFuture config.maxApp oracle) compiler cache optimized
    targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache optimizedRun lowerRun tailRun tmcRun inlineRun
    cacheEq distinct oracleDistinct oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker
    lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq bvlNonfail
  exact optimizedEq.trans closureEq

/-- Future BVL code after enabled incremental multi-argument introduction. -/
noncomputable abbrev mtiClosureFuture {C : Type} (maxApp : Nat)
    (oracle : ClosSem.CompileOracle (Nat × C)) : BvlSem.CompileOracle C :=
  closureFuture maxApp (pureCo (ClosMti.compileInc maxApp) ∘ oracle)

/-- Enabled multi-argument introduction followed by closure conversion, BVL
optimization, lowering and the implemented BVI passes preserves the current
Lean observations under the stated oracle, cache and counter assumptions.
Known-function and direct-call conversion remain disabled, and the evaluator
correspondence has not yet been reviewed against HOL. -/
theorem mti_closure_optimized_bvi_semantics {C F : Type} (ffi : HolFfiState F)
    (closureFuel bvlFuel inlineLimit cutSize bviFuel optFuel : Nat) (splitSeq tailEnabled tmcEnabled : Bool)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × OptimizationConfig C)) (compiler : BviSem.Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNext : Nat) (lowered beforeTmc afterTmc final : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (enabled : config.doMti = true) (calls : config.doCall = false) (known : config.knownConf = none)
    (positive : 1 ≤ config.maxApp)
    (unary : ∀ e ∈ expressions, noMti e)
    (oracleUnary : ∀ index, (oracle index).2.2 = [] ∧ ∀ e ∈ (oracle index).2.1, noMti e)
    (preprocess : compileCommonNoOpts? { config with doMti := false }
      (ClosMti.introList config.maxApp expressions) = some (current, program))
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq compiled = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel output.start 0 optimized = some (targetStart, lowered, targetNext))
    (tailRun : BviTailrec.compileProgFuel bviFuel tailEnabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, final))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc config.maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler))))) expressions ≠ .fail)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ oracle))
    (initialBound : current.nextLoc ≤ (oracle 0).1.1)
    (cacheEq : (mtiClosureFuture config.maxApp oracle 0).1.1 = cache)
    (oracleTailBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp oracle i).1.2.2.1)
    (oracleTailWorker : ∀ i, BviTailrec.inWorkerNamespace (mtiClosureFuture config.maxApp oracle i).1.2.2.1)
    (oracleTmcBound : ∀ i, bvlNumStubs ≤ (mtiClosureFuture config.maxApp oracle i).1.2.2.2.1)
    (oracleTmcWorker : ∀ i, BviTmc.inWorkerNamespace (mtiClosureFuture config.maxApp oracle i).1.2.2.2.1)
    (lowerCounterBound : targetNext ≤ (mtiClosureFuture config.maxApp oracle 0).1.2.1)
    (tailCounterBound : tailLast ≤ (mtiClosureFuture config.maxApp oracle 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (mtiClosureFuture config.maxApp oracle 0).1.2.2.2.1)
    (bviCacheEq : (mtiClosureFuture config.maxApp oracle 0).1.2.2.2.2.1 = bviCache) :
    BviSem.semantics ffi (sptFromAList final)
      (stateCo BviInline.compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
        (stateCo (BviTailrec.compileProgSource tailEnabled) (stateCo BvlToBvi.compileIncSource
          (BvlInline.Proofs.letOpOracle splitSeq cutSize
            (BvlInline.Proofs.removeTicksCo ∘ BvlInline.Proofs.inCo inlineLimit (mtiClosureFuture config.maxApp oracle)))))))
      compiler targetStart =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (pureCc (ClosMti.compileInc config.maxApp)
          (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc
            (pureCc (compileInc config.maxApp) (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler))))) expressions := by
  let transformedOracle : ClosSem.CompileOracle (Nat × OptimizationConfig C) :=
    pureCo (ClosMti.compileInc config.maxApp) ∘ oracle
  have closureEq := compileCallMtiFuel_mtiOnly_semantics ffi closureFuel config current output expressions
    program compiled names oracle (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler)
    enabled calls known positive unary oracleUnary preprocess closureRun nonfail oracleState initialBound
  have bvlNonfail : BvlSem.semantics ffi (sptFromAList compiled) (mtiClosureFuture config.maxApp oracle)
      (optimizationCallback inlineLimit cutSize splitSeq tailEnabled tmcEnabled compiler) output.start ≠ .fail := by
    rw [closureEq]
    exact nonfail
  obtain ⟨current', program', output', names', pre', compiled', _⟩ :=
    compileCallMtiFuel_mtiOnly_erasure closureFuel config output expressions compiled names enabled calls known closureRun
  have equal := Option.some.inj (pre'.symm.trans preprocess)
  cases equal
  have distinct := compileNoOpts_prepared_labels_nodup { config with doMti := false } current output'
    (ClosMti.introList config.maxApp expressions) program compiled names' pre' compiled'
  have oracleDistinct : ∀ i, (((mtiClosureFuture config.maxApp oracle) i).2.map Prod.fst).Nodup := by
    apply numberedAnnotatedOracle_labels_nodup_emptyAux config.maxApp transformedOracle
    intro i
    rfl
  have optimizedEq := BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_semantics bvlFuel inlineLimit cutSize bviFuel optFuel
    output.start 0 splitSeq tailEnabled tmcEnabled ffi compiled (mtiClosureFuture config.maxApp oracle) compiler cache optimized
    targetStart targetNext lowered beforeTmc afterTmc final tailLast tmcLast bviCache optimizedRun lowerRun tailRun tmcRun inlineRun
    cacheEq distinct oracleDistinct oracleTailBound oracleTailWorker oracleTmcBound oracleTmcWorker
    lowerCounterBound tailCounterBound tmcCounterBound bviCacheEq bvlNonfail
  exact optimizedEq.trans closureEq

end Flapjack.Compiler.Backend.ClosToBvl
