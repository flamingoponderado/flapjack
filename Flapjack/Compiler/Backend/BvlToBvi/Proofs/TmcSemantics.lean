import Flapjack.Compiler.Backend.BvlToBvi.Proofs.NoMutcons
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TailrecSemantics
import Flapjack.Compiler.Backend.BviTmc.Proofs.Observation

/-! Semantic handoff from BVI tail recursion to tail-modulo-cons. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Flapjack pipeline infrastructure: the executed BVI tail-recursion and
TMC passes preserve the behavior of the lowered program. Future-oracle
conditions remain explicit, as do the original non-failure conditions. -/
theorem lowering_tailrec_tmc_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (lowered beforeTmc afterTmc : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (ffi : HolFfiState F) (oracle : BviSem.CompileOracle (Nat × (Nat × C)))
    (compiler : BviSem.Compiler C) (entry : Nat)
    (distinct : (program.map Prod.fst).Nodup)
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel true (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (tailOracleCondition : ∀ n, BviTailrec.inputCondition (oracle n).1.1 (oracle n).2)
    (tailCounterBound : tailLast ≤ (oracle 0).1.1)
    (tmcOracleCondition : ∀ n, BviTmc.inputCondition
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle n).1.1
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle n).2)
    (tmcWorkerBound : ∀ n, n ∈ afterTmc.map Prod.fst → BviTmc.inWorkerNamespace n →
      n < (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle 0).1.1)
    (notFail : BviSem.semantics ffi (sptFromAList lowered) oracle
      (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCc BviTmc.compileEachSource compiler)) entry ≠ .fail) :
    BviSem.semantics ffi (sptFromAList lowered) oracle
        (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc BviTmc.compileEachSource compiler)) entry =
      BviSem.semantics ffi (sptFromAList afterTmc)
        (BackendProps.stateCo BviTmc.compileEachSource
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle)) compiler entry := by
  have tailSame := lowering_tailrec_semantics fuel optFuel start counter targetStart targetCounter enabled
    program lowered beforeTmc tailLast ffi oracle (BackendProps.stateCc BviTmc.compileEachSource compiler) entry
    distinct lowerRun tailRun tailOracleCondition tailCounterBound notFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList beforeTmc)
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle)
      (BackendProps.stateCc BviTmc.compileEachSource compiler) entry ≠ .fail := by
    rw [← tailSame]
    exact notFail
  have condition := lowered_tailrec_tmc_inputCondition_complete fuel optFuel start counter targetStart targetCounter
    enabled program lowered beforeTmc tailLast distinct lowerRun tailRun
  have tmcSame := BviTmc.Observation.compileProgFuel_enabled_semantics fuel (bvlNumStubs + 3) entry
    beforeTmc afterTmc tmcLast ffi (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle) compiler
    condition tmcOracleCondition tmcWorkerBound tmcRun tmcNonFail
  exact tailSame.trans tmcSame

/-- Flapjack pipeline infrastructure: BVL lowering, BVI tail recursion,
and enabled TMC preserve a non-failing source program's behavior. Oracle
conditions for the successive passes remain explicit. -/
theorem lowerThenTailrecTmc_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × (Nat × (Nat × C)))) (compiler : BviSem.Compiler C)
    (lowered beforeTmc afterTmc : List (Nat × Nat × Bvi.Exp)) (tailLast tmcLast : Nat)
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel true (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (distinct : (program.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (program.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ n, BvlHandle.Proofs.handleOk ((oracle n).2.map (fun (_, _, body) => body)))
    (oracleDistinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (oracleNextBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.1)
    (oracleWorker : ∀ n, BviTailrec.inWorkerNamespace (oracle n).1.2.1)
    (lowerCounterBound : targetCounter ≤ (oracle 0).1.1)
    (tailCounterBound : tailLast ≤ (oracle 0).1.2.1)
    (tmcOracleCondition : ∀ n, BviTmc.inputCondition
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle) n).1.1
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle) n).2)
    (tmcWorkerBound : ∀ n, n ∈ afterTmc.map Prod.fst → BviTmc.inWorkerNamespace n →
      n < (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle) 0).1.1)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCc BviTmc.compileEachSource compiler))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList afterTmc)
        (BackendProps.stateCo BviTmc.compileEachSource
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle)))
        compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc BviTmc.compileEachSource compiler))) start := by
  have previous := lowerThenTailrec_semantics fuel optFuel start counter targetStart targetCounter enabled ffi program
    oracle (BackendProps.stateCc BviTmc.compileEachSource compiler) lowered beforeTmc tailLast lowerRun tailRun
    distinct handlers oracleHandlers oracleDistinct oracleNextBound oracleWorker lowerCounterBound tailCounterBound nonFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList beforeTmc)
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle))
      (BackendProps.stateCc BviTmc.compileEachSource compiler) targetStart ≠ .fail := by
    rw [previous]
    exact nonFail
  have condition := lowered_tailrec_tmc_inputCondition_complete fuel optFuel start counter targetStart targetCounter
    enabled program lowered beforeTmc tailLast distinct lowerRun tailRun
  have tmcSame := BviTmc.Observation.compileProgFuel_enabled_semantics fuel (bvlNumStubs + 3) targetStart
    beforeTmc afterTmc tmcLast ffi
    (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle))
    compiler condition tmcOracleCondition tmcWorkerBound tmcRun tmcNonFail
  exact tmcSame.symm.trans previous

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
