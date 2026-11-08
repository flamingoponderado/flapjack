import Flapjack.Compiler.Backend.ClosToBvl.FullIncremental
import Flapjack.Compiler.Backend.ClosToBvl.Incremental
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileProduction
import Flapjack.Compiler.Backend.ClosCall.Proofs.TotalCorrespondence

/-! Executable correspondence for the full incremental closure-to-BVL pass. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private theorem prepareIncMtiFuel_eq_source (fuel : Nat) (config : Config)
    (program : ClosSem.Program) :
    prepareIncMtiFuel? fuel config program =
      some (ClosMti.condCompileInc config.doMti config.maxApp program) := by
  cases h : config.doMti <;>
    simp [prepareIncMtiFuel?, ClosMti.condCompileInc, ClosMti.compileInc,
      ClosMti.compileFuel_eq_compile, ClosMti.compile, h]

/-- The bounded executable incremental path agrees with the complete HOL
composition for every fuel, configuration and input. This is a Flapjack
production-correspondence theorem, not a separate HOL declaration. -/
theorem compileIncFuel_eq_source (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    compileIncFuel? fuel config program = some (closToBvlCompileInc config program) := by
  unfold compileIncFuel?
  rw [prepareIncMtiFuel_eq_source]
  simp only [bind, Option.bind]
  generalize numberedEq : ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc
    (ClosMti.condCompileInc config.doMti config.maxApp program) = numbered
  rcases numbered with ⟨next, numbered⟩
  rw [ClosKnown.compileIncFuel_eq_source]
  generalize knownEq : ClosKnown.knownCompileInc (ClosKnown.knownStaticConf config.knownConf)
    (ClosKnown.optionValApproxSpt config.knownConf) numbered = optimized
  rcases optimized with ⟨globals, optimized⟩
  simp only
  cases callFlag : config.doCall <;>
    simp [ClosCall.compileIncFuel_eq_compileInc, ClosCall.condCallCompileInc, callFlag,
      compileInc, compileProg_checked_eq_original, closToBvlCompileInc, numberedEq, knownEq]

end Flapjack.Compiler.Backend.ClosToBvl
