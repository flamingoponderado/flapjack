import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Divergence
import Flapjack.Compiler.Backend.BviToData.Proofs.Semantics
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TmcSemantics
import Flapjack.Compiler.Backend.BviInline.Proofs.Observation

/-! Composition of the BVL-to-BVI and BVI-to-data semantic simulations. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack
open Flapjack.Compiler.Backend.BvlInline.Proofs

/-- The executed BVL-to-BVI lowering followed by BVI-to-data compilation
preserves a non-failing BVL program's observable behavior. The source-program,
handler, and future-oracle conditions are the premises of the lowering proof.
This is Flapjack pipeline infrastructure pending HOL evaluator and carrier
reviews for the constituent simulations. -/
theorem compileProgFuel_toData_semantics {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : DataSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (limits : DataSem.Limits) (sizes : Spt Nat)
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (nonfail : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource (fun cfg code => compiler cfg (BviToData.compileProg code))) start ≠ .fail) :
    DataSem.semantics ffi (sptFromAList (BviToData.compileProg targetProgram))
      (fun index => let (cfg, code) := BackendProps.stateCo compileIncSource oracle index
        (cfg, BviToData.compileProg code)) compiler limits sizes targetStart =
    BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource (fun cfg code => compiler cfg (BviToData.compileProg code))) start := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let bviOracle := BackendProps.stateCo compileIncSource oracle
  have lowerSame := compileProgFuel_semantics fuel optFuel start counter ffi programs oracle bviCompiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound nonfail
  have bviNonFail : BviSem.semantics ffi (sptFromAList targetProgram) bviOracle bviCompiler targetStart ≠ .fail := by
    rw [lowerSame]
    exact nonfail
  have dataSame := BviToData.compileProg_semantics ffi targetProgram bviOracle compiler limits sizes targetStart bviNonFail
  exact dataSame.trans lowerSame

/-- BVL lowering, tail recursion, TMC, inlining, and BVI-to-data compilation
preserve observable behavior under the established pass and oracle conditions.
This is Lean-side composition pending HOL evaluator and carrier review. -/
theorem lowerTailrecTmcInline_toData_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled tmcEnabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × (Nat × (Nat × (Spt (Nat × Bvi.Exp) × C)))))
    (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (lowered beforeTmc afterTmc output : List (Nat × Nat × Bvi.Exp)) (tailLast tmcLast : Nat)
    (cache : Spt (Nat × Bvi.Exp))
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel fuel afterTmc = some (cache, output))
    (distinct : (program.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (program.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ n, BvlHandle.Proofs.handleOk ((oracle n).2.map (fun (_, _, body) => body)))
    (oracleDistinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (oracleNextBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.1)
    (oracleWorker : ∀ n, BviTailrec.inWorkerNamespace (oracle n).1.2.1)
    (lowerCounterBound : targetCounter ≤ (oracle 0).1.1)
    (tailCounterBound : tailLast ≤ (oracle 0).1.2.1)
    (oracleTmcBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.1)
    (oracleTmcWorker : ∀ n, BviTmc.inWorkerNamespace (oracle n).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (oracle 0).1.2.2.1)
    (inlineOracleCache : ((BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCo compileIncSource oracle))) 0).1.1 = cache)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCc BviInline.compileIncSource
            (fun cfg code => compiler cfg (BviToData.compileProg code)))))) start ≠ .fail) :
    DataSem.semantics ffi (sptFromAList (BviToData.compileProg output))
      (fun n => let (cfg, code) := (BackendProps.stateCo BviInline.compileIncSource
        (BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled)
            (BackendProps.stateCo compileIncSource oracle)))) n
        (cfg, BviToData.compileProg code)) compiler limits sizes targetStart =
    BvlSem.semantics ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCc BviInline.compileIncSource
            (fun cfg code => compiler cfg (BviToData.compileProg code)))))) start := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let tmcOracle := BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
    (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle))
  let inlineOracle := BackendProps.stateCo BviInline.compileIncSource tmcOracle
  have previous := lowerThenTailrecTmc_semantics fuel optFuel start counter targetStart targetCounter enabled tmcEnabled
    ffi program oracle (BackendProps.stateCc BviInline.compileIncSource bviCompiler) lowered beforeTmc afterTmc tailLast tmcLast
    lowerRun tailRun tmcRun distinct handlers oracleHandlers oracleDistinct oracleNextBound oracleWorker
    lowerCounterBound tailCounterBound oracleTmcBound oracleTmcWorker tmcCounterBound nonFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList afterTmc) tmcOracle
      (BackendProps.stateCc BviInline.compileIncSource bviCompiler) targetStart ≠ .fail := by
    rw [previous]
    exact nonFail
  have condition := lowered_tailrec_tmc_inputCondition_complete fuel optFuel start counter targetStart targetCounter
    enabled program lowered beforeTmc tailLast distinct lowerRun tailRun
  have tmcSource : BviTmc.compileProgSource tmcEnabled (bvlNumStubs + 3) beforeTmc = (tmcLast, afterTmc) := by
    have equality := BviTmc.compileProgFuel_eq_source fuel tmcEnabled (bvlNumStubs + 3) beforeTmc
    rw [tmcRun] at equality
    exact (Option.some.inj equality).symm
  have tmcDistinct : (afterTmc.map Prod.fst).Nodup :=
    (BviTmc.compileProgSource_distinct_and_free tmcEnabled (bvlNumStubs + 3) tmcLast beforeTmc afterTmc
      tmcSource condition.2.2.1 condition.1).1
  have inlineSame := BviInline.Observation.compileProgFuel_semantics fuel afterTmc output cache tmcOracle bviCompiler
    ffi targetStart inlineRun inlineOracleCache tmcDistinct tmcNonFail
  have inlineNonFail : BviSem.semantics ffi (sptFromAList output) inlineOracle bviCompiler targetStart ≠ .fail := by
    rw [inlineSame]
    exact tmcNonFail
  have dataSame := BviToData.compileProg_semantics ffi output inlineOracle compiler limits sizes targetStart inlineNonFail
  exact dataSame.trans (inlineSame.trans previous)

/-- The configured BVL optimizer, BVL lowering, three BVI optimizations, and
BVI-to-data lowering preserve a non-failing program's observable behavior,
under the future-oracle and counter conditions of the component passes. This
is Lean-side composition pending HOL evaluator and carrier review. -/
theorem optimizedLowerTailrecTmcInline_toData_semantics {C F : Type}
    (bvlFuel inlineLimit cutSize bviFuel optFuel start counter : Nat) (splitSeq enabled tmcEnabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × (Nat × (Nat × (Nat × (Spt (Nat × Bvi.Exp) × C))))))
    (compiler : DataSem.Compiler C) (limits : DataSem.Limits) (sizes : Spt Nat)
    (bvlCache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetCounter : Nat) (lowered beforeTmc afterTmc output : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq program = some (bvlCache, optimized))
    (lowerRun : compileProgFuel bviFuel optFuel start counter optimized = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel bviFuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, output))
    (cacheEq : (oracle 0).1.1 = bvlCache)
    (distinct : (program.map Prod.fst).Nodup)
    (oracleDistinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (oracleTailBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.1)
    (oracleTailWorker : ∀ n, BviTailrec.inWorkerNamespace (oracle n).1.2.2.1)
    (oracleTmcBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.2.1)
    (oracleTmcWorker : ∀ n, BviTmc.inWorkerNamespace (oracle n).1.2.2.2.1)
    (lowerCounterBound : targetCounter ≤ (oracle 0).1.2.1)
    (tailCounterBound : tailLast ≤ (oracle 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (oracle 0).1.2.2.2.1)
    (inlineOracleCache : ((BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource
        (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle))))) 0).1.1 = bviCache)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled)
            (BackendProps.stateCc BviInline.compileIncSource
              (fun cfg code => compiler cfg (BviToData.compileProg code))))))))) start ≠ .fail) :
    DataSem.semantics ffi (sptFromAList (BviToData.compileProg output))
      (fun n => let (cfg, code) := (BackendProps.stateCo BviInline.compileIncSource
        (BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource
            (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)))))) n
        (cfg, BviToData.compileProg code)) compiler limits sizes targetStart =
    BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled)
            (BackendProps.stateCc BviInline.compileIncSource
              (fun cfg code => compiler cfg (BviToData.compileProg code))))))))) start := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let future := letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)
  let tmcOracle := BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
    (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource future))
  let inlineOracle := BackendProps.stateCo BviInline.compileIncSource tmcOracle
  have previous := optimizedLowerTailrecTmc_semantics bvlFuel inlineLimit cutSize bviFuel optFuel start counter
    splitSeq enabled tmcEnabled ffi program oracle (BackendProps.stateCc BviInline.compileIncSource bviCompiler)
    bvlCache optimized targetStart targetCounter lowered beforeTmc afterTmc tailLast tmcLast optimizedRun
    lowerRun tailRun tmcRun cacheEq distinct oracleDistinct oracleTailBound oracleTailWorker oracleTmcBound
    oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound nonFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList afterTmc) tmcOracle
      (BackendProps.stateCc BviInline.compileIncSource bviCompiler) targetStart ≠ .fail := by
    rw [previous]
    exact nonFail
  have optimizedDistinct : (optimized.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProgFuel_names bvlFuel inlineLimit cutSize splitSeq program bvlCache optimized optimizedRun]
    exact distinct
  have condition := lowered_tailrec_tmc_inputCondition_complete bviFuel optFuel start counter targetStart targetCounter
    enabled optimized lowered beforeTmc tailLast optimizedDistinct lowerRun tailRun
  have tmcSource : BviTmc.compileProgSource tmcEnabled (bvlNumStubs + 3) beforeTmc = (tmcLast, afterTmc) := by
    have equality := BviTmc.compileProgFuel_eq_source bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc
    rw [tmcRun] at equality
    exact (Option.some.inj equality).symm
  have tmcDistinct : (afterTmc.map Prod.fst).Nodup :=
    (BviTmc.compileProgSource_distinct_and_free tmcEnabled (bvlNumStubs + 3) tmcLast beforeTmc afterTmc
      tmcSource condition.2.2.1 condition.1).1
  have inlineSame := BviInline.Observation.compileProgFuel_semantics bviFuel afterTmc output bviCache tmcOracle bviCompiler
    ffi targetStart inlineRun inlineOracleCache tmcDistinct tmcNonFail
  have inlineNonFail : BviSem.semantics ffi (sptFromAList output) inlineOracle bviCompiler targetStart ≠ .fail := by
    rw [inlineSame]
    exact tmcNonFail
  have dataSame := BviToData.compileProg_semantics ffi output inlineOracle compiler limits sizes targetStart inlineNonFail
  exact dataSame.trans (inlineSame.trans previous)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
