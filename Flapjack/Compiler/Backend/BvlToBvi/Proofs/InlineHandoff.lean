import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TmcSemantics
import Flapjack.Compiler.Backend.BviInline.Proofs.Observation

/-! Observable BVL-to-BVI pipeline through BVI inlining. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open BviTailrec BvlInline.Proofs

/-- Flapjack pipeline infrastructure: the executed BVL optimizer, lowering,
BVI tail recursion, TMC, and inliner preserve non-failing BVL observations.
Oracle namespace, counter, and inliner-cache conditions remain explicit;
the underlying HOL evaluator and carrier comparisons are still pending. -/
theorem optimizedLowerTailrecTmcInline_semantics {C F : Type}
    (bvlFuel inlineLimit cutSize bviFuel optFuel start counter : Nat) (splitSeq enabled tmcEnabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × (Nat × (Nat × (Nat × (Spt (Nat × Bvi.Exp) × C))))))
    (compiler : BviSem.Compiler C) (cache : Spt (Nat × Bvl.Exp))
    (optimized : List (Nat × Nat × Bvl.Exp)) (targetStart targetCounter : Nat)
    (lowered beforeTmc afterTmc output : List (Nat × Nat × Bvi.Exp)) (tailLast tmcLast : Nat)
    (bviCache : Spt (Nat × Bvi.Exp))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq program = some (cache, optimized))
    (lowerRun : compileProgFuel bviFuel optFuel start counter optimized = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel bviFuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, output))
    (cacheEq : (oracle 0).1.1 = cache)
    (distinct : (program.map Prod.fst).Nodup)
    (oracleDistinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (oracleTailBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.1)
    (oracleTailWorker : ∀ n, BviTailrec.inWorkerNamespace (oracle n).1.2.2.1)
    (oracleTmcBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.2.1)
    (oracleTmcWorker : ∀ n, BviTmc.inWorkerNamespace (oracle n).1.2.2.2.1)
    (lowerCounterBound : targetCounter ≤ (oracle 0).1.2.1)
    (tailCounterBound : tailLast ≤ (oracle 0).1.2.2.1)
    (tmcCounterBound : tmcLast ≤ (oracle 0).1.2.2.2.1)
    (bviCacheEq : (oracle 0).1.2.2.2.2.1 = bviCache)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled)
            (BackendProps.stateCc BviInline.compileIncSource compiler))))))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList output)
        (BackendProps.stateCo BviInline.compileIncSource (BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource
            (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)))))) compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
          (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
            (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled)
              (BackendProps.stateCc BviInline.compileIncSource compiler))))))) start := by
  let future := letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)
  let bviOracle := BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
    (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource future))
  have previous := optimizedLowerTailrecTmc_semantics bvlFuel inlineLimit cutSize bviFuel optFuel start counter
    splitSeq enabled tmcEnabled ffi program oracle (BackendProps.stateCc BviInline.compileIncSource compiler)
    cache optimized targetStart targetCounter lowered beforeTmc afterTmc tailLast tmcLast
    optimizedRun lowerRun tailRun tmcRun cacheEq distinct oracleDistinct oracleTailBound oracleTailWorker
    oracleTmcBound oracleTmcWorker lowerCounterBound tailCounterBound tmcCounterBound nonFail
  have middleNotFail : BviSem.semantics ffi (sptFromAList afterTmc) bviOracle
      (BackendProps.stateCc BviInline.compileIncSource compiler) targetStart ≠ .fail := by
    rw [previous]
    exact nonFail
  have optimizedDistinct : (optimized.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProgFuel_names bvlFuel inlineLimit cutSize splitSeq program cache optimized optimizedRun]
    exact distinct
  have condition := lowered_tailrec_tmc_inputCondition_complete bviFuel optFuel start counter targetStart targetCounter
    enabled optimized lowered beforeTmc tailLast optimizedDistinct lowerRun tailRun
  have tmcSource : BviTmc.compileProgSource tmcEnabled (bvlNumStubs + 3) beforeTmc = (tmcLast, afterTmc) := by
    have correspondence := BviTmc.compileProgFuel_eq_source bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc
    rw [tmcRun] at correspondence
    exact (Option.some.inj correspondence).symm
  have afterTmcDistinct : (afterTmc.map Prod.fst).Nodup :=
    (BviTmc.compileProgSource_distinct_and_free tmcEnabled (bvlNumStubs + 3) tmcLast
      beforeTmc afterTmc tmcSource condition.2.2.1 condition.1).1
  have oracleCache : (bviOracle 0).1.1 = bviCache := by
    dsimp [bviOracle, BackendProps.stateCo]
    rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle 0]
    exact bviCacheEq
  have inlining := BviInline.Observation.compileProgFuel_semantics bviFuel afterTmc output bviCache
    bviOracle compiler ffi targetStart inlineRun oracleCache afterTmcDistinct middleNotFail
  exact inlining.trans previous

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
