import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `ConditionalSelect@64`

`arm8_ast` uses this instruction in the `addOverflow` and `subOverflow`
lowerings (`ConditionalSelect@64 (1, false, true, 7, 31, 31, s)`): the zero
register selects either `0` or `1`, i.e. the overflow flag.  This module
records the word, its `Encode`/`Decode` inverse and the `Run` semantics.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- Four-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_four (w : BitVec 4) : holV2w 4 [w[3], w[2], w[1], w[0]] = w :=
  holV2w_holW2v w

/-- The word emitted for `ConditionalSelect@64`: HOL's `e_data` term
`1 ++ op ++ 011010100 ++ Rm ++ cond ++ 0 ++ o2 ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8ConditionalSelectWord (op o2 : Bool) (cond : BitVec 4) (rm rn rd : BitVec 5) :
    BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (holV2w 1 [op] ++
      BitVec.setWidth 30 ((BitVec.ofNat 9 212) ++
        BitVec.setWidth 21 (rm ++
          BitVec.setWidth 16 (cond ++
            BitVec.setWidth 12 ((0 : BitVec 1) ++
              BitVec.setWidth 11 (holV2w 1 [o2] ++
                BitVec.setWidth 10 (rn ++ rd))))))))

/-- `e_data` of `ConditionalSelect@64` is the select word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_conditionalSelect (op o2 : Bool) (cond : BitVec 4)
    (rm rn rd : BitVec 5) :
    e_data (.«ConditionalSelect@64» ((1 : BitVec 64), (op, (o2, (cond, (rm, (rn, rd))))))) =
      MachineCode.ARM8 (arm8ConditionalSelectWord op o2 cond rm rn rd) := by
  rfl

/-- `Encode` of `ConditionalSelect@64` is the select word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_conditionalSelect (op o2 : Bool) (cond : BitVec 4)
    (rm rn rd : BitVec 5) :
    Encode (.Data (.«ConditionalSelect@64» ((1 : BitVec 64), (op, (o2, (cond, (rm, (rn, rd)))))))) =
      MachineCode.ARM8 (arm8ConditionalSelectWord op o2 cond rm rn rd) := by
  simp only [Encode, arm8EData_conditionalSelect]

/-- The rendered `Decode` inverts `arm8ConditionalSelectWord` for the
`else_inv = false`, `else_inc = true` form used by `arm8_ast`. -/
theorem arm8Decode_conditionalSelect (cond : BitVec 4) (rm rn rd : BitVec 5) :
    Decode (arm8ConditionalSelectWord false true cond rm rn rd) =
      instruction.Data (Data.«ConditionalSelect@64»
        ((1 : BitVec 64), (false, (true, (cond, (rm, (rn, rd))))))) := by
  simp only [arm8ConditionalSelectWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_one_true, holV2w_four, holV2w_five]

/-- The four encoded bytes of `ConditionalSelect@64`. -/
theorem arm8EncodeBytes_conditionalSelect (op o2 : Bool) (cond : BitVec 4)
    (rm rn rd : BitVec 5) :
    arm8Encode (.Data (.«ConditionalSelect@64»
      ((1 : BitVec 64), (op, (o2, (cond, (rm, (rn, rd)))))))) =
      [BitVec.ofNat 8 ((arm8ConditionalSelectWord op o2 cond rm rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8ConditionalSelectWord op o2 cond rm rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8ConditionalSelectWord op o2 cond rm rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8ConditionalSelectWord op o2 cond rm rn rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_conditionalSelect]

/-- `Run` of `ConditionalSelect@64`: write `Rn` when the condition holds, and
otherwise `Rm` (optionally inverted and/or incremented) to `Rd`. -/
theorem arm8Run_conditionalSelect (op o2 : Bool) (cond : BitVec 4)
    (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«ConditionalSelect@64»
      ((1 : BitVec 64), (op, (o2, (cond, (rm, (rn, rd)))))))) st =
      (let s : BitVec 64 × arm8_state :=
        (if ConditionHolds cond st then (X (TN := 64) rn st, st)
          else ((if o2 then (if op then ~~~(X (TN := 64) rm st) else X (TN := 64) rm st) + 1
                else (if op then ~~~(X (TN := 64) rm st) else X (TN := 64) rm st)), st))
      «write'X» (s.1, rd) s.2) := by
  simp only [Run, «dfn'ConditionalSelect»]
  rfl

end Flapjack.Compiler.Encoders.Arm8.L3
