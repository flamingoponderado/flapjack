module

public import Flapjack.Compiler.Backend.ClosToBvl.FullIncremental
public import Flapjack.Compiler.Backend.ClosToBvl.Incremental
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileProduction
public import Flapjack.Compiler.Backend.ClosCall.Proofs.TotalCorrespondence

@[expose] public section

/-! Executable correspondence for the full incremental closure-to-BVL pass. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The bounded executable incremental path agrees with the complete HOL
composition for every fuel, configuration and input. This is a Flapjack
production-correspondence theorem, not a separate HOL declaration. -/
theorem compileIncFuel_eq_source (fuel : Nat) (config : Config) (program : ClosSem.Program) :
    compileIncFuel? fuel config program = some (closToBvlCompileInc config program) := by
  cases mtiFlag : config.doMti <;> cases callFlag : config.doCall <;>
    simp [compileIncFuel?, prepareIncMtiFuel?, ClosMti.compileFuel_eq_compile,
      ClosMti.condCompileInc, ClosMti.compileInc, ClosMti.compile,
      ClosKnown.compileIncFuel_eq_source, ClosCall.compileIncFuel_eq_compileInc,
      ClosCall.condCallCompileInc, compileInc, compileProg_checked_eq_original,
      closToBvlCompileInc, ClosAnnotate.compileIncSource_eq_compileInc,
      extractNameSource_eq_extractName, mtiFlag, callFlag]

end Flapjack.Compiler.Backend.ClosToBvl
