import Flapjack.Compiler.Backend.WordCse.RegisterData
import Flapjack.Compiler.Encoders.Asm

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

/-- Original full FP canonicalization. The first register is retained even
for Fma and both cross-register moves; every remaining register is canonicalized.
Executed FP routing remains separate from this native definition. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalFp_def"]
def canonicalFp (data : Knowledge) : HolFp → HolFp
  | .fpLess first second third => .fpLess first (canonicalRegs data second) (canonicalRegs data third)
  | .fpLessEqual first second third => .fpLessEqual first (canonicalRegs data second) (canonicalRegs data third)
  | .fpEqual first second third => .fpEqual first (canonicalRegs data second) (canonicalRegs data third)
  | .fpAbs first second => .fpAbs first (canonicalRegs data second)
  | .fpNeg first second => .fpNeg first (canonicalRegs data second)
  | .fpSqrt first second => .fpSqrt first (canonicalRegs data second)
  | .fpAdd first second third => .fpAdd first (canonicalRegs data second) (canonicalRegs data third)
  | .fpSub first second third => .fpSub first (canonicalRegs data second) (canonicalRegs data third)
  | .fpMul first second third => .fpMul first (canonicalRegs data second) (canonicalRegs data third)
  | .fpDiv first second third => .fpDiv first (canonicalRegs data second) (canonicalRegs data third)
  | .fpFma first second third => .fpFma first (canonicalRegs data second) (canonicalRegs data third)
  | .fpMov first second => .fpMov first (canonicalRegs data second)
  | .fpMovToReg first second third => .fpMovToReg first (canonicalRegs data second) (canonicalRegs data third)
  | .fpMovFromReg first second third => .fpMovFromReg first (canonicalRegs data second) (canonicalRegs data third)
  | .fpToInt first second => .fpToInt first (canonicalRegs data second)
  | .fpFromInt first second => .fpFromInt first (canonicalRegs data second)

end Flapjack.Compiler.Backend.WordCse
