import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Carry

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `ConditionalCompareImmediate@64`

`arm8_ast` uses this instruction in the `addCarry` lowering
(`ConditionalCompareImmediate@64 (1, false, 0, 0, (false, false, true, false),
resultCarry)`): it compares `resultCarry` with zero and stores the resulting
condition flags.  This module records the word, the `e_sf` field and the `Run`
semantics; the conditional `e_data` and the decoder inverse are still open.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `e_sf` at the 64-bit width is always one (the `sf` bit of the L3 encoding). -/
theorem e_sf_sixtyfour (sf : BitVec 64) : e_sf (TN := 64) sf = (1 : BitVec 1) := by
  simp [e_sf, holV2w_one_true]

/-- The word emitted for `ConditionalCompareImmediate@64` when the immediate
fits five bits: HOL's `e_data` term
`1 ++ opc ++ 111010010 ++ imm5 ++ cond ++ 10 ++ Rn ++ 0 ++ nzcv` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8ConditionalCompareWord (opc : Bool) (imm5 : BitVec 5) (cd : BitVec 4)
    (n z c v : Bool) (rn : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (holV2w 1 [opc] ++
      BitVec.setWidth 30 ((BitVec.ofNat 9 466) ++
        BitVec.setWidth 21 (imm5 ++
          BitVec.setWidth 16 (cd ++
            BitVec.setWidth 12 ((BitVec.ofNat 2 2) ++
              BitVec.setWidth 10 (rn ++
                BitVec.setWidth 5 ((BitVec.ofNat 1 0) ++
                  BitVec.setWidth 4 (holV2w 1 [n] ++
                    BitVec.setWidth 3 (holV2w 1 [z] ++
                      BitVec.setWidth 2 (holV2w 1 [c] ++ holV2w 1 [v])))))))))))

/-- `Run` of `ConditionalCompareImmediate@64`: when the condition holds, compare
`Rn` with the immediate through `AddWithCarry` and store the flags; otherwise
store the literal `nzcv` field. -/
theorem arm8Run_conditionalCompare (opc : Bool) (imm : BitVec 64) (cd : BitVec 4)
    (n z c v : Bool) (rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«ConditionalCompareImmediate@64»
      ((1 : BitVec 64), (opc, (imm, (cd, ((n, (z, (c, v))), rn))))))) st =
      (if ConditionHolds cd st then
        (match (if opc then ((~~~imm), true) else (imm, false)) with
         | (operand2, carry_in) =>
           (match AddWithCarry (TN := 64) (X (TN := 64) rn st, operand2, carry_in) with
            | (_u_, flags) => SetTheFlags (true, flags) st))
       else SetTheFlags (true, (n, (z, (c, v)))) st) := by
  simp only [Run, «dfn'ConditionalCompareImmediate»]

end Flapjack.Compiler.Encoders.Arm8.L3
