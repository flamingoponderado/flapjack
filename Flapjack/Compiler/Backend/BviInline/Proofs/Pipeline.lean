import Flapjack.Compiler.Backend.BviInline.Proofs.Observation
import Flapjack.Compiler.Backend.BviTmc.Proofs.Observation

/-! Composition of the BVI TMC and inlining compiler passes. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BackendProps

/-- Flapjack infrastructure: the executed whole-program inliner and tick
remover preserve function labels in their original order. -/
theorem compileProgFuel_names (fuel : Nat) (program output : List (Nat × Nat × Bvi.Exp))
    (cache : Spt (Nat × Bvi.Exp)) (run : BviInline.compileProgFuel fuel program = some (cache, output)) :
    output.map Prod.fst = program.map Prod.fst := by
  have sourceRun := compileProgFuel_eq_source fuel program
  rw [run] at sourceRun
  have same : compileIncSource .ln program = (cache, output) := (Option.some.inj sourceRun).symm
  have names := inlineAllSource_names program .ln
  cases inlineRun : inlineAllSource .ln program with
  | mk finalCache inlined =>
    have outputEq : cleanProg inlined = output := by
      simpa [compileIncSource, inlineRun, cleanProg] using congrArg Prod.snd same
    rw [← outputEq, cleanProg_names]
    simpa [inlineRun] using names

/-- Flapjack infrastructure: the executed TMC and BVI inlining stages
preserve whole-program observations in sequence, using the TMC input
condition to establish the inliner's distinct-label requirement. The
underlying evaluator and carrier correspondence remains to be reviewed. -/
theorem tmc_inline_semantics {C F : Type} (fuel : Nat) (enabled : Bool) (next start : Nat)
    (program intermediate output : List (Nat × Nat × Bvi.Exp)) (last : Nat)
    (cache : Spt (Nat × Bvi.Exp)) (ffi : HolFfiState F)
    (oracle : BviSem.CompileOracle (Nat × (Spt (Nat × Bvi.Exp) × C)))
    (compiler : BviSem.Compiler C)
    (condition : BviTmc.inputCondition next program)
    (oracleConditions : ∀ n, BviTmc.inputCondition (oracle n).1.1 (oracle n).2)
    (workerBound : ∀ n, n ∈ intermediate.map Prod.fst → BviTmc.inWorkerNamespace n → n < (oracle 0).1.1)
    (tmcRun : BviTmc.compileProgFuel fuel enabled next program = some (last, intermediate))
    (inlineRun : BviInline.compileProgFuel fuel intermediate = some (cache, output))
    (inlineOracleCache : ((stateCo (BviTmc.compileProgSource enabled) oracle) 0).1.1 = cache)
    (notFail : BviSem.semantics ffi (sptFromAList program) oracle
      (stateCc (BviTmc.compileProgSource enabled) (stateCc compileIncSource compiler)) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList output)
        (stateCo compileIncSource (stateCo (BviTmc.compileProgSource enabled) oracle)) compiler start =
      BviSem.semantics ffi (sptFromAList program) oracle
        (stateCc (BviTmc.compileProgSource enabled) (stateCc compileIncSource compiler)) start := by
  have sourceRun : BviTmc.compileProgSource enabled next program = (last, intermediate) := by
    have correspondence := BviTmc.compileProgFuel_eq_source fuel enabled next program
    rw [tmcRun] at correspondence
    exact (Option.some.inj correspondence).symm
  have distinct : (intermediate.map Prod.fst).Nodup :=
    (BviTmc.compileProgSource_distinct_and_free enabled next last program intermediate sourceRun
      condition.2.2.1 condition.1).1
  have tmcSemantics := BviTmc.Observation.compileProgFuel_semantics fuel enabled next start
    program intermediate last ffi oracle (stateCc compileIncSource compiler)
    condition oracleConditions workerBound tmcRun notFail
  have middleNotFail : BviSem.semantics ffi (sptFromAList intermediate)
      (stateCo (BviTmc.compileProgSource enabled) oracle) (stateCc compileIncSource compiler) start ≠ .fail := by
    rw [← tmcSemantics]
    exact notFail
  have inlineSemantics := Observation.compileProgFuel_semantics fuel intermediate output cache
    (stateCo (BviTmc.compileProgSource enabled) oracle) compiler ffi start inlineRun
    inlineOracleCache distinct middleNotFail
  exact inlineSemantics.trans tmcSemantics.symm

/-- Flapjack infrastructure: the configured BVI tail-recursion, TMC, and
inlining traversals preserve observable behavior in sequence. Pass input,
oracle, and worker bounds are explicit pending the upstream pipeline proof;
the evaluator and carriers still require HOL source review. -/
theorem tailrec_tmc_inline_semantics {C F : Type} (fuel : Nat)
    (tailEnabled tmcEnabled : Bool) (tailNext tmcNext start : Nat)
    (program afterTail afterTmc output : List (Nat × Nat × Bvi.Exp)) (tailLast tmcLast : Nat)
    (cache : Spt (Nat × Bvi.Exp)) (ffi : HolFfiState F)
    (oracle : BviSem.CompileOracle (Nat × (Nat × (Spt (Nat × Bvi.Exp) × C))))
    (compiler : BviSem.Compiler C)
    (tailCondition : BviTailrec.inputCondition tailNext program)
    (tailOracleConditions : ∀ n, BviTailrec.inputCondition (oracle n).1.1 (oracle n).2)
    (tailWorkerBound : ∀ n, n ∈ afterTail.map Prod.fst → BviTailrec.inWorkerNamespace n → n < (oracle 0).1.1)
    (tailRun : BviTailrec.compileProgFuel fuel tailEnabled tailNext program = some (tailLast, afterTail))
    (tmcCondition : BviTmc.inputCondition tmcNext afterTail)
    (tmcOracleConditions : ∀ n, BviTmc.inputCondition
      ((stateCo (BviTailrec.compileProgSource tailEnabled) oracle) n).1.1
      ((stateCo (BviTailrec.compileProgSource tailEnabled) oracle) n).2)
    (tmcWorkerBound : ∀ n, n ∈ afterTmc.map Prod.fst → BviTmc.inWorkerNamespace n →
      n < ((stateCo (BviTailrec.compileProgSource tailEnabled) oracle) 0).1.1)
    (tmcRun : BviTmc.compileProgFuel fuel tmcEnabled tmcNext afterTail = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel fuel afterTmc = some (cache, output))
    (inlineOracleCache : ((stateCo (BviTmc.compileProgSource tmcEnabled)
      (stateCo (BviTailrec.compileProgSource tailEnabled) oracle)) 0).1.1 = cache)
    (notFail : BviSem.semantics ffi (sptFromAList program) oracle
      (stateCc (BviTailrec.compileProgSource tailEnabled)
        (stateCc (BviTmc.compileProgSource tmcEnabled) (stateCc compileIncSource compiler))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList output)
        (stateCo compileIncSource (stateCo (BviTmc.compileProgSource tmcEnabled)
          (stateCo (BviTailrec.compileProgSource tailEnabled) oracle))) compiler start =
      BviSem.semantics ffi (sptFromAList program) oracle
        (stateCc (BviTailrec.compileProgSource tailEnabled)
          (stateCc (BviTmc.compileProgSource tmcEnabled) (stateCc compileIncSource compiler))) start := by
  have tailSemantics := BviTailrec.compileProgFuel_semantics fuel tailEnabled tailNext program ffi oracle
    (stateCc (BviTmc.compileProgSource tmcEnabled) (stateCc compileIncSource compiler))
    start tailLast afterTail tailCondition tailOracleConditions tailWorkerBound tailRun notFail
  have afterTailNotFail : BviSem.semantics ffi (sptFromAList afterTail)
      (stateCo (BviTailrec.compileProgSource tailEnabled) oracle)
      (stateCc (BviTmc.compileProgSource tmcEnabled) (stateCc compileIncSource compiler)) start ≠ .fail := by
    rw [← tailSemantics]
    exact notFail
  have restSemantics := tmc_inline_semantics fuel tmcEnabled tmcNext start afterTail afterTmc output
    tmcLast cache ffi (stateCo (BviTailrec.compileProgSource tailEnabled) oracle) compiler
    tmcCondition tmcOracleConditions tmcWorkerBound tmcRun inlineRun inlineOracleCache afterTailNotFail
  exact restSemantics.trans tailSemantics.symm

end Flapjack.Compiler.Backend.BviInline
