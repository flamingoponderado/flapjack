module

public import Flapjack.Compiler.Backend.ClosToBvl.WholeProgram
public import Flapjack.Compiler.Backend.ClosToBvl.Common
public import Flapjack.Compiler.Backend.ClosToBvl.Prepared
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileProduction
public import Flapjack.Compiler.Backend.ClosCall.Proofs.TotalCorrespondence
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence

@[expose] public section

/-! Connect the executed closure compiler with the original definition. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The bounded production compiler returns the source compiler's whole result.
This Flapjack-specific correspondence is not a separate HOL declaration. -/
theorem compileCallMtiFuel_eq_source (fuel : Nat) (config : Config)
    (expressions : List ClosLang.Exp) :
    compileCallMtiFuel? fuel config expressions = some (compileSource config expressions) := by
  simp [compileCallMtiFuel?, compileCommon, ClosMti.compileFuel_eq_compile,
    ClosKnown.compileFuel_eq_source, ClosCall.compileFuel_eq_compile,
    ClosAnnotate.compileSource_eq_compile, compileSource, compilePrepared?,
    compileProg_checked_eq_original]

end Flapjack.Compiler.Backend.ClosToBvl
