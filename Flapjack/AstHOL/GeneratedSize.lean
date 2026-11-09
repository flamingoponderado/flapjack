import Flapjack.AstHOL.LitOp
import Flapjack.Basis.Pure.MlString.Size

namespace Flapjack.AstHOL

/-- HOL's automatically generated `lit_size` for `ast$lit`. There is no
separate source declaration to tag; its complete typed equations and concrete
evaluations are captured in `flat_elim_value_globals_probe.out`. This is a
prerequisite for the original generated flat-value size and theorems using
that size, rather than Lean's different `sizeOf`. -/
def litSizeHOL : Lit → Nat
  | .intLit _ => 1
  | .char c => 1 + holCharSize c
  | .strLit s => 1 + mlstringSizeHOL s
  | .word8 w => 1 + w.toNat
  | .word64 w => 1 + w.toNat
  | .float64 w => 1 + w.toNat

end Flapjack.AstHOL
