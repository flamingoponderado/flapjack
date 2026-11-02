import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The `Loc` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Loc r i` to a single `Address` instruction when `i` is in the
signed 20-bit range, and to a six-instruction sequence otherwise.  This module
records the `Address` instruction facts: the word, its `Encode`/`Decode`
inverse and its `Run` semantics.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `Address` with page `false`: HOL's `e_data` term
`0 ++ immlo ++ 10000 ++ immhi ++ Rd`. -/
def arm8AddressWord (imm : BitVec 64) (rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 1 0) ++
    BitVec.setWidth 31 (holWordExtract 2 1 0 imm ++
      BitVec.setWidth 29 ((BitVec.ofNat 5 16) ++
        BitVec.setWidth 24 (holWordExtract 19 20 2 imm ++ rd))))

/-- `Encode` of an in-range `Address` is the address word. -/
theorem arm8Encode_address (imm : BitVec 64) (rd : BitVec 5)
    (h : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm) :
    Encode (.Address (false, (imm, rd))) = MachineCode.ARM8 (arm8AddressWord imm rd) := by
  simp only [Encode, arm8AddressWord, Bool.false_eq_true, if_false]
  rw [h]
  simp

/-- `Run` of `Address` with page `false` writes `PC + imm` to `Rd`. -/
theorem arm8Run_address (imm : BitVec 64) (rd : BitVec 5) (st : arm8_state) :
    Run (.Address (false, (imm, rd))) st = «write'X» ((st.PC + imm), rd) st := by
  simp only [Run, «dfn'Address», Bool.false_eq_true, if_false]

end Flapjack.Compiler.Encoders.Arm8.L3
