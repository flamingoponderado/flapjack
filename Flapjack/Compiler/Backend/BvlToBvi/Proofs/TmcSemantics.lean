import Flapjack.Compiler.Backend.BvlToBvi.Proofs.NoMutcons
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TailrecSemantics
import Flapjack.Compiler.Backend.BviTmc.Proofs.Observation

/-! Semantic handoff from BVI tail recursion to tail-modulo-cons. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open BviTailrec BvlInline.Proofs

/-- Flapjack pipeline infrastructure: each future BVL oracle program, after
lowering and tail-recursion compilation, satisfies the TMC input condition
when its labels are distinct and both worker counters use their namespaces. -/
theorem lowered_oracle_tmc_inputCondition {C : Type} (enabled : Bool)
    (oracle : BvlSem.CompileOracle (Nat × (Nat × (Nat × C))))
    (distinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (tailBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.1)
    (tailWorker : ∀ n, BviTailrec.inWorkerNamespace (oracle n).1.2.1)
    (tmcBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.1)
    (tmcWorker : ∀ n, BviTmc.inWorkerNamespace (oracle n).1.2.2.1) :
    ∀ n, BviTmc.inputCondition
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle) n).1.1
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle) n).2 := by
  intro n
  let lower := compileIncSource (oracle n).1.1 (oracle n).2
  let tail := BviTailrec.compileProgSource enabled (oracle n).1.2.1 lower.2
  have tailCondition : BviTailrec.inputCondition (oracle n).1.2.1 lower.2 :=
    compileIncSource_tailrec_inputCondition (oracle n).1.1 (oracle n).1.2.1 (oracle n).2
      (distinct n) (tailBound n) (tailWorker n)
  have outside : ∀ name ∈ lower.2.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name := by
    intro name member _
    exact compileIncSource_outside_tmc_namespace (oracle n).1.1 (oracle n).2 name member
  have safe : ∀ entry ∈ lower.2, BviTmc.noMutcons entry.2.2 :=
    compileIncSource_noMutcons (oracle n).1.1 lower.1 (oracle n).2 lower.2 (Prod.eta lower).symm
  have tailRun : BviTailrec.compileProgFuel 0 enabled (oracle n).1.2.1 lower.2 = some (tail.1, tail.2) := by
    rw [BviTailrec.compileProgFuel_eq_source]
  have condition := tailrec_output_tmc_inputCondition_of_input_noMutcons 0 enabled (oracle n).1.2.1 tail.1
    (oracle n).1.2.2.1 lower.2 tail.2 tailCondition outside safe (tmcBound n) (tmcWorker n) tailRun
  exact condition

/-- Flapjack pipeline infrastructure: every worker label in an executed TMC
output is below its returned worker counter in either pass mode. -/
theorem tmc_output_worker_below_counter (fuel : Nat) (enabled : Bool) (next last : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (condition : BviTmc.inputCondition next program)
    (run : BviTmc.compileProgFuel fuel enabled next program = some (last, output)) :
    ∀ name ∈ output.map Prod.fst, BviTmc.inWorkerNamespace name → name < last := by
  cases enabled with
  | false =>
    simp [BviTmc.compileProgFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    intro name member worker
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    by_cases below : name < bvlNumStubs
    · have nextBound := condition.2.2.2.2.1
      omega
    · have outside := condition.2.2.2.1 entry
        (List.mem_filter.mpr ⟨present, by simpa [same] using (show bvlNumStubs ≤ name by omega)⟩)
      exact (outside (by simpa [same] using worker)).elim
  | true =>
    have pair := Option.some.inj ((BviTmc.compileProgFuel_eq_source fuel true next program).symm.trans run)
    have codeEq : (BviTmc.compileEachSource next program).2 = output := congrArg Prod.snd pair
    have nextEq : (BviTmc.compileEachSource next program).1 = last := congrArg Prod.fst pair
    intro name member worker
    have present : sptMem name (sptFromAList (BviTmc.compileEachSource next program).2) := by
      apply (BviTailrec.sptFromAList_mem_iff _ name).mpr
      simpa [codeEq] using member
    have bound := BviTmc.compileEachSource_install_worker_bound next program condition name ⟨present, worker⟩
    simpa [nextEq] using bound

/-- Flapjack pipeline infrastructure: the executed BVI tail-recursion and
TMC passes preserve the behavior of the lowered program. Future-oracle
conditions remain explicit, as do the original non-failure conditions. -/
theorem lowering_tailrec_tmc_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled tmcEnabled : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (lowered beforeTmc afterTmc : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (ffi : HolFfiState F) (oracle : BviSem.CompileOracle (Nat × (Nat × C)))
    (compiler : BviSem.Compiler C) (entry : Nat)
    (distinct : (program.map Prod.fst).Nodup)
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (tailOracleCondition : ∀ n, BviTailrec.inputCondition (oracle n).1.1 (oracle n).2)
    (tailCounterBound : tailLast ≤ (oracle 0).1.1)
    (tmcOracleCondition : ∀ n, BviTmc.inputCondition
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle n).1.1
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle n).2)
    (tmcWorkerBound : ∀ n, n ∈ afterTmc.map Prod.fst → BviTmc.inWorkerNamespace n →
      n < (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle 0).1.1)
    (notFail : BviSem.semantics ffi (sptFromAList lowered) oracle
      (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler)) entry ≠ .fail) :
    BviSem.semantics ffi (sptFromAList lowered) oracle
        (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler)) entry =
      BviSem.semantics ffi (sptFromAList afterTmc)
        (BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle)) compiler entry := by
  have tailSame := lowering_tailrec_semantics fuel optFuel start counter targetStart targetCounter enabled
    program lowered beforeTmc tailLast ffi oracle (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler) entry
    distinct lowerRun tailRun tailOracleCondition tailCounterBound notFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList beforeTmc)
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle)
      (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler) entry ≠ .fail := by
    rw [← tailSame]
    exact notFail
  have condition := lowered_tailrec_tmc_inputCondition_complete fuel optFuel start counter targetStart targetCounter
    enabled program lowered beforeTmc tailLast distinct lowerRun tailRun
  have tmcSame := BviTmc.Observation.compileProgFuel_semantics fuel tmcEnabled (bvlNumStubs + 3) entry
    beforeTmc afterTmc tmcLast ffi (BackendProps.stateCo (BviTailrec.compileProgSource enabled) oracle) compiler
    condition tmcOracleCondition tmcWorkerBound tmcRun tmcNonFail
  exact tailSame.trans tmcSame

/-- Flapjack pipeline infrastructure: BVL lowering, BVI tail recursion,
and TMC preserve a non-failing source program's behavior. Oracle
conditions for the successive passes remain explicit. -/
theorem lowerThenTailrecTmc_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled tmcEnabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × (Nat × (Nat × C)))) (compiler : BviSem.Compiler C)
    (lowered beforeTmc afterTmc : List (Nat × Nat × Bvi.Exp)) (tailLast tmcLast : Nat)
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
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
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList afterTmc)
        (BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle)))
        compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (BviTailrec.compileProgSource enabled)
          (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler))) start := by
  have previous := lowerThenTailrec_semantics fuel optFuel start counter targetStart targetCounter enabled ffi program
    oracle (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler) lowered beforeTmc tailLast lowerRun tailRun
    distinct handlers oracleHandlers oracleDistinct oracleNextBound oracleWorker lowerCounterBound tailCounterBound nonFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList beforeTmc)
      (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle))
      (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler) targetStart ≠ .fail := by
    rw [previous]
    exact nonFail
  have condition := lowered_tailrec_tmc_inputCondition_complete fuel optFuel start counter targetStart targetCounter
    enabled program lowered beforeTmc tailLast distinct lowerRun tailRun
  have tmcOracleCondition := lowered_oracle_tmc_inputCondition enabled oracle oracleDistinct oracleNextBound oracleWorker
    oracleTmcBound oracleTmcWorker
  have tmcWorkerBound : ∀ n, n ∈ afterTmc.map Prod.fst → BviTmc.inWorkerNamespace n →
      n < (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle) 0).1.1 := by
    intro name member worker
    have below := tmc_output_worker_below_counter fuel tmcEnabled (bvlNumStubs + 3) tmcLast beforeTmc afterTmc
      condition tmcRun name member worker
    exact Nat.lt_of_lt_of_le below tmcCounterBound
  have tmcSame := BviTmc.Observation.compileProgFuel_semantics fuel tmcEnabled (bvlNumStubs + 3) targetStart
    beforeTmc afterTmc tmcLast ffi
    (BackendProps.stateCo (BviTailrec.compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle))
    compiler condition tmcOracleCondition tmcWorkerBound tmcRun tmcNonFail
  exact tmcSame.symm.trans previous

/-- Flapjack pipeline infrastructure: the BVL optimizer, lowering,
tail-recursion pass, and TMC preserve a non-failing program's BVL
behavior, using the executed output of each pass. -/
theorem optimizedLowerTailrecTmc_semantics {C F : Type}
    (bvlFuel inlineLimit cutSize bviFuel optFuel start counter : Nat) (splitSeq enabled tmcEnabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × (Nat × (Nat × (Nat × C)))))
    (compiler : BviSem.Compiler C) (cache : Spt (Nat × Bvl.Exp))
    (optimized : List (Nat × Nat × Bvl.Exp)) (targetStart targetCounter : Nat)
    (lowered beforeTmc afterTmc : List (Nat × Nat × Bvi.Exp)) (tailLast tmcLast : Nat)
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq program = some (cache, optimized))
    (lowerRun : compileProgFuel bviFuel optFuel start counter optimized = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel bviFuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
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
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled)
          (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler)))))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList afterTmc)
        (BackendProps.stateCo (BviTmc.compileProgSource tmcEnabled)
          (BackendProps.stateCo (compileProgSource enabled) (BackendProps.stateCo compileIncSource
            (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle))))) compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
          (BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled)
            (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler)))))) start := by
  let future := letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)
  have previous := optimizedLowerTailrec_semantics bvlFuel inlineLimit cutSize bviFuel optFuel start counter
    splitSeq enabled ffi program oracle (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler) cache optimized
    targetStart targetCounter lowered beforeTmc tailLast optimizedRun lowerRun tailRun cacheEq distinct oracleDistinct
    oracleTailBound oracleTailWorker lowerCounterBound tailCounterBound nonFail
  have tmcNonFail : BviSem.semantics ffi (sptFromAList beforeTmc)
      (BackendProps.stateCo (compileProgSource enabled) (BackendProps.stateCo compileIncSource future))
      (BackendProps.stateCc (BviTmc.compileProgSource tmcEnabled) compiler) targetStart ≠ .fail := by
    rw [previous]
    exact nonFail
  have optimizedDistinct : (optimized.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProgFuel_names bvlFuel inlineLimit cutSize splitSeq program cache optimized optimizedRun]
    exact distinct
  have condition := lowered_tailrec_tmc_inputCondition_complete bviFuel optFuel start counter targetStart targetCounter
    enabled optimized lowered beforeTmc tailLast optimizedDistinct lowerRun tailRun
  have futureDistinct : ∀ n, ((future n).2.map Prod.fst).Nodup := by
    intro n
    rw [optimizedOracle_names inlineLimit cutSize splitSeq oracle n]
    exact oracleDistinct n
  have futureTailBound : ∀ n, bvlNumStubs ≤ (future n).1.2.1 := by
    intro n; rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle n]; exact oracleTailBound n
  have futureTailWorker : ∀ n, BviTailrec.inWorkerNamespace (future n).1.2.1 := by
    intro n; rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle n]; exact oracleTailWorker n
  have futureTmcBound : ∀ n, bvlNumStubs ≤ (future n).1.2.2.1 := by
    intro n; rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle n]; exact oracleTmcBound n
  have futureTmcWorker : ∀ n, BviTmc.inWorkerNamespace (future n).1.2.2.1 := by
    intro n; rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle n]; exact oracleTmcWorker n
  have futureCondition := lowered_oracle_tmc_inputCondition enabled future futureDistinct futureTailBound futureTailWorker
    futureTmcBound futureTmcWorker
  have counterBound : tmcLast ≤ (future 0).1.2.2.1 := by
    rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle 0]
    exact tmcCounterBound
  have workerBound : ∀ n, n ∈ afterTmc.map Prod.fst → BviTmc.inWorkerNamespace n →
      n < (BackendProps.stateCo (compileProgSource enabled) (BackendProps.stateCo compileIncSource future) 0).1.1 := by
    intro n member worker
    exact Nat.lt_of_lt_of_le (tmc_output_worker_below_counter bviFuel tmcEnabled (bvlNumStubs + 3) tmcLast
      beforeTmc afterTmc condition tmcRun n member worker) counterBound
  have tmcSame := BviTmc.Observation.compileProgFuel_semantics bviFuel tmcEnabled (bvlNumStubs + 3) targetStart
    beforeTmc afterTmc tmcLast ffi (BackendProps.stateCo (compileProgSource enabled) (BackendProps.stateCo compileIncSource future))
    compiler condition futureCondition workerBound tmcRun tmcNonFail
  exact tmcSame.symm.trans previous

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
