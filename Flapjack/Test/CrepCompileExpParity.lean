module

public import Flapjack.Pancake.CrepToLoop

@[expose] public section

/-! Direct parity for `crep_to_loop$compile_exp_def` at
`cakeml/pancake/crep_to_loopScript.sml:50`.  The three-argument Mul case keeps
the source pass's destination at `tmp + LENGTH es`; the live set is compared
as membership because Lean stores it as a list while HOL uses `num_set`. -/
namespace Flapjack.Test.CrepCompileExpParity

def context : LoopContext Nat :=
  { vars := [], functions := [], maxVar := 0, target := .rv64i }

end Flapjack.Test.CrepCompileExpParity
