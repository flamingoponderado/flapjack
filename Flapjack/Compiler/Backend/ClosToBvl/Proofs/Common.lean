module

public import Flapjack.Compiler.Backend.ClosToBvl.Common
public import Flapjack.Compiler.Backend.ClosToBvl.Prepared
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileProduction
public import Flapjack.Compiler.Backend.ClosCall.Proofs.TotalCorrespondence

@[expose] public section

/-! The production closure preprocessing path follows the source definition. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The executed bounded passes reach the original `compile_common` result.
This Flapjack-specific equation connects the HOL definition to the executable
compiler; it is not a separate HOL theorem. -/
theorem compileCallMtiFuel_eq_common (fuel : Nat) (config : Config)
    (expressions : List ClosLang.Exp) :
    compileCallMtiFuel? fuel config expressions =
      let (current, program) := compileCommon config expressions
      compilePrepared? config current expressions program := by
  simp [compileCallMtiFuel?, compileCommon, ClosMti.compileFuel_eq_compile,
    ClosKnown.compileFuel_eq_source, ClosCall.compileFuel_eq_compile,
    ClosAnnotate.compileSource_eq_compile]

end Flapjack.Compiler.Backend.ClosToBvl
