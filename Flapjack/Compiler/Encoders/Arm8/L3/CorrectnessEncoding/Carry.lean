module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ConditionalSelect

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `AddSubCarry@64`

`arm8_ast` uses this instruction twice in the `addCarry` lowering: once with
`setflags := true` to compute the destination and once with `setflags := false`
to carry the result into the second source register.  This module records the
word, its `Encode`/`Decode` inverse and the `Run` semantics through
`AddWithCarry` and `SetTheFlags`.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `AddSubCarry@64`: HOL's `e_data` term
`1 ++ opc ++ s ++ 11010000 ++ Rm ++ 000000 ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8AddSubCarryWord (opc s : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (holV2w 1 [opc] ++
      BitVec.setWidth 30 (holV2w 1 [s] ++
        BitVec.setWidth 29 ((BitVec.ofNat 8 208) ++
          BitVec.setWidth 21 (rm ++
            BitVec.setWidth 16 ((BitVec.ofNat 6 0) ++
              BitVec.setWidth 10 (rn ++ rd)))))))

/-- `e_data` of `AddSubCarry@64` is the add-with-carry word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_addSubCarry (opc s : Bool) (rm rn rd : BitVec 5) :
    e_data (.«AddSubCarry@64» ((1 : BitVec 64), (opc, (s, (rm, (rn, rd)))))) =
      MachineCode.ARM8 (arm8AddSubCarryWord opc s rm rn rd) := by
  rfl

/-- `Encode` of `AddSubCarry@64` is the add-with-carry word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_addSubCarry (opc s : Bool) (rm rn rd : BitVec 5) :
    Encode (.Data (.«AddSubCarry@64» ((1 : BitVec 64), (opc, (s, (rm, (rn, rd))))))) =
      MachineCode.ARM8 (arm8AddSubCarryWord opc s rm rn rd) := by
  simp only [Encode, arm8EData_addSubCarry]

/-- The rendered `Decode` inverts `arm8AddSubCarryWord` for the
`opc = false`, `s = true` form used first by `arm8_ast`. -/
theorem arm8Decode_addSubCarry (rm rn rd : BitVec 5) :
    Decode (arm8AddSubCarryWord false true rm rn rd) =
      instruction.Data (Data.«AddSubCarry@64»
        ((1 : BitVec 64), (false, (true, (rm, (rn, rd)))))) := by
  simp only [arm8AddSubCarryWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_one_true, holV2w_five]

/-- `Run` of `AddSubCarry@64`: add `Rn`, `Rm` (optionally inverted) and the
carry flag through `AddWithCarry`, write the result to `Rd`, and set the flags
when `s` is set. -/
theorem arm8Run_addSubCarry (opc s : Bool) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«AddSubCarry@64»
      ((1 : BitVec 64), (opc, (s, (rm, (rn, rd))))))) st =
      (let v0 : BitVec 64 := X (TN := 64) rm st
       match AddWithCarry (TN := 64) (X (TN := 64) rn st, (if opc then ~~~v0 else v0), st.PSTATE.C) with
       | (result, nzcv) => «write'X» (result, rd) (SetTheFlags (s, nzcv) st)) := by
  simp only [Run, «dfn'AddSubCarry»]

end Flapjack.Compiler.Encoders.Arm8.L3
