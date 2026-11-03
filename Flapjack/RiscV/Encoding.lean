import Flapjack.RiscV.Encoding.NativeInstruction
import Flapjack.Compiler.Encoders.RiscV.Target

/-!
# RISC-V instruction encoding

This is the concrete artifact boundary corresponding to CakeML's
`riscv_encode`/`riscv_enc`.  The typed instruction model is encoded as one
32-bit RV instruction and then emitted in little-endian byte order, matching
the `word8 list` produced by the HOL target encoder.
-/

namespace Flapjack.RiscV

def encodeWordBytes (value : BitVec 32) : List (BitVec 8) :=
  [value.extractLsb' 0 8, value.extractLsb' 8 8,
   value.extractLsb' 16 8, value.extractLsb' 24 8]

/-- Source-order native byte slices; this relation is Flapjack infrastructure. -/
theorem encodeWordBytes_eq_extracts (value : BitVec 32) :
    encodeWordBytes value =
      [value.extractLsb' 0 8, value.extractLsb' 8 8,
       value.extractLsb' 16 8, value.extractLsb' 24 8] := rfl

structure EncodedRiscVSection (width : Nat) where
  label : Nat
  address : Word width
  bytes : List (BitVec 8)
  deriving Repr

end Flapjack.RiscV
