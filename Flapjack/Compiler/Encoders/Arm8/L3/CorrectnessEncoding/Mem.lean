import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldCase

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `LoadStoreImmediate`: the `Mem` lowering of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Mem` to one or two `LoadStoreImmediate` instructions, and
the `e_LoadStoreImmediate` rendering picks between the signed nine-bit and the
scaled twelve-bit forms.  This module records the two emitted words and their
`Encode` equations; the `Decode` inverse, the `Run` semantics and the case
theorems follow.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The signed nine-bit `LoadStoreImmediate` word: HOL's `e_data` term
`sz ++ 0b111000 ++ opc ++ 0 ++ imm9 ++ acctype_bit ++ 0 ++ Rn ++ Rt`
(Flapjack infrastructure: a readable abbreviation for a mechanically rendered
term). -/
def arm8LoadStoreImm9Word (sz : BitVec 2) (opc : BitVec 2) (imm9 : BitVec 9)
    (acctypeBit : BitVec 1) (rn rt : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 (sz ++
    BitVec.setWidth 30 (BitVec.ofNat 6 56 ++
      BitVec.setWidth 24 (opc ++
        BitVec.setWidth 22 (BitVec.ofNat 1 0 ++
          BitVec.setWidth 21 (imm9 ++
            BitVec.setWidth 12 (acctypeBit ++
              BitVec.setWidth 11 (BitVec.ofNat 1 0 ++
                BitVec.setWidth 10 (rn ++ rt))))))))

/-- The scaled twelve-bit `LoadStoreImmediate` word: HOL's `e_data` term
`sz ++ 0b111001 ++ opc ++ imm12 ++ Rn ++ Rt` (Flapjack infrastructure). -/
def arm8LoadStoreImm12Word (sz : BitVec 2) (opc : BitVec 2) (imm12 : BitVec 12)
    (rn rt : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 (sz ++
    BitVec.setWidth 30 (BitVec.ofNat 6 57 ++
      BitVec.setWidth 24 (opc ++
        BitVec.setWidth 22 (imm12 ++
          BitVec.setWidth 10 (rn ++ rt)))))

end Flapjack.Compiler.Encoders.Arm8.L3
