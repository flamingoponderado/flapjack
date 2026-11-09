module

public import Flapjack.Compiler.Backend.BvlConst.SourceCompile
public import Flapjack.Compiler.Backend.BvlConst.Proofs.CompileProduction

@[expose] public section

/-! Executable correspondence for the source constant-propagation entry point. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl

/-- The executed bounded traversal returns the total source expression result.
This Flapjack bridge connects the production adapter to `compile_exp_def`. -/
theorem compileBounded_eq_compileExp (fuel : Nat) (e : Exp) :
    compileBounded fuel [] e = some (compileExp e) := by
  simpa [compileExp_eq] using compileBounded_eq fuel [] e

end Flapjack.Compiler.Backend.BvlConst
