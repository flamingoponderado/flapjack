module

public import Flapjack.Pancake.CrepToLoop

@[expose] public section

/-! Direct parity for `crep_to_loop$compile_crepop` at line 42. -/
namespace Flapjack.Test.CompileCrepOpParity

def originalCompileCrepOp : List (LoopProg Nat) × Nat :=
  ([.arith (.longMul 4 4 2 3)], 4)

end Flapjack.Test.CompileCrepOpParity
