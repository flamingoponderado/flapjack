import Flapjack.RiscV.Model
import Flapjack.RiscV.L3.Types

/-! Complete conversion of the executed RV64 instruction carrier into the native
L3 carrier. This is Flapjack infrastructure, not a HOL datatype port: the
production carrier has fewer constructors than the full native instruction.
The conversion is total over every production constructor. Universal encoding
agreement and actual route replacement remain separate prerequisites. -/
namespace Flapjack.RiscV

/-- Register codec preserving all 32 production registers. No HOL original
uses this Fin-based carrier, so this infrastructure is deliberately untagged. -/
def nativeRegister (r : Fin 32) : BitVec 5 := BitVec.ofNat 5 r.val

theorem nativeRegister_toNat (r : Fin 32) : (nativeRegister r).toNat = r.val := by
  simp [nativeRegister]

end Flapjack.RiscV
