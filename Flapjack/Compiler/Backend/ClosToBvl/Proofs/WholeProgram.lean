module

public import Flapjack.Compiler.Backend.ClosToBvl.WholeProgram
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Common
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence

@[expose] public section

/-! Connect the executed closure compiler with the original definition. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The bounded production compiler returns the source compiler's whole result.
This Flapjack-specific correspondence is not a separate HOL declaration. -/
theorem compileCallMtiFuel_eq_source (fuel : Nat) (config : Config)
    (expressions : List ClosLang.Exp) :
    compileCallMtiFuel? fuel config expressions = some (compileSource config expressions) := by
  rw [compileCallMtiFuel_eq_common]
  simp [compileSource, compilePrepared?, compileProg_checked_eq_original]

end Flapjack.Compiler.Backend.ClosToBvl
