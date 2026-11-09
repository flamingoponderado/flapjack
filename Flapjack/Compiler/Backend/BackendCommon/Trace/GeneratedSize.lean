import Flapjack.Compiler.Backend.BackendCommon.Trace

namespace Flapjack.Compiler.Backend.BackendCommon

/-- HOL's datatype-generated `tra_size`; the full typed equations and a
concrete evaluation are in `flat_elim_value_globals_probe.out`. It is used in
the original flat-expression size, not Lean's generated `sizeOf`. -/
def traSizeHOL : Tra → Nat
  | .sourceLoc a b c d => 1 + (a + (b + (c + d)))
  | .cons tr n => 1 + (traSizeHOL tr + n)
  | .union left right => 1 + (traSizeHOL left + traSizeHOL right)
  | .none => 0

end Flapjack.Compiler.Backend.BackendCommon
