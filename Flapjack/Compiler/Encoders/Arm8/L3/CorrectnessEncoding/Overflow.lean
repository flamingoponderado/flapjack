import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Arith
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Carry

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# `AddOverflow` and `SubOverflow`

`arm8_ast` lowers both to an `AddSubShiftedRegister@64` with `S := true` followed
by a `ConditionalSelect@64` on `VC` (`0b0111`): the select writes `0` when the
overflow flag is clear and `1` otherwise, into the result-carry register.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `ConditionHolds` at `0b0111` (`VC`) is "the overflow flag is clear". -/
theorem arm8ConditionHolds_seven (st : arm8_state) :
    ConditionHolds (7 : BitVec 4) st = !st.PSTATE.V := by
  simp only [ConditionHolds, ConditionTest, Flapjack.RiscV.L3.holWordExtract]
  rfl

/-- `Run` of a flag-setting `AddSubShiftedRegister@64` with an `lsl` shift. -/
theorem arm8Run_addSubShiftedRegister_setflags (op : Bool) (rm : BitVec 5) (amount : BitVec 6)
    (rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (true, (ShiftType.lsl, (rm, (amount, (rn, rd))))))))) st =
      let p := if op then (~~~ShiftReg (TN := 64) (rm, ShiftType.lsl, amount.toNat) st, true)
        else (ShiftReg (TN := 64) (rm, ShiftType.lsl, amount.toNat) st, false)
      let r := AddWithCarry (X rn st, p.1, p.2)
      write'X (r.1, rd) (SetTheFlags (true, r.2) st) := by
  cases op <;>
    simp only [Run, «dfn'AddSubShiftedRegister», SetTheFlags, Bool.false_eq_true, if_true,
      if_false]

/-- `Run` of the `ConditionalSelect@64` that `arm8_ast` emits after the
flag-setting add: write `0` when `VC` holds and `1` otherwise. -/
theorem arm8Run_conditionalSelect_zero (rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«ConditionalSelect@64»
      ((1 : BitVec 64), (false, (true, ((7 : BitVec 4),
        ((31 : BitVec 5), ((31 : BitVec 5), rd)))))))) st =
      «write'X» ((if ConditionHolds (7 : BitVec 4) st then (0 : BitVec 64) else 1), rd) st := by
  rw [arm8Run_conditionalSelect]
  simp only [arm8X_zero_ofNat]
  cases hC : ConditionHolds (7 : BitVec 4) st <;> simp

/-- The state equation of a flag-setting `AddSubShiftedRegister@64` with an
`lsl` shift by zero: `Rd` receives `Rn + Rm` (or `Rn - Rm`), and `PSTATE`'s
flags come from `AddWithCarry`. -/
theorem arm8Run_addSubShiftedRegister_setflags_eq (op : Bool) (rm rn : BitVec 5) (rd : Nat)
    (st : arm8_state) (hrd : rd ≠ 31) (hlt : rd < 32) :
    Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (true, (ShiftType.lsl, (rm, (0, (rn, BitVec.ofNat 5 rd))))))))) st =
      { st with
        REG := holUpdate (BitVec.ofNat 5 rd)
          (AddWithCarry (TN := 64) (X (TN := 64) rn st,
            (if op then ~~~X (TN := 64) rm st else X (TN := 64) rm st, op))).1 st.REG,
        PSTATE :=
          { st.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (if op then ~~~X (TN := 64) rm st else X (TN := 64) rm st, op))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (if op then ~~~X (TN := 64) rm st else X (TN := 64) rm st, op))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (if op then ~~~X (TN := 64) rm st else X (TN := 64) rm st, op))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (if op then ~~~X (TN := 64) rm st else X (TN := 64) rm st, op))).2.2.2.2 } } := by
  rw [arm8Run_addSubShiftedRegister_setflags]
  dsimp only
  rw [arm8WriteX_of_valid _ _ hrd hlt]
  cases op <;> simp [SetTheFlags, ShiftReg, ShiftValue]

/-- One `arm8Next` step on the flag-setting `AddSubShiftedRegister@64` word:
`Rd` receives `Rn + Rm` (or `Rn - Rm`), `PSTATE`'s flags come from
`AddWithCarry`, and `PC` advances by four. -/
theorem arm8Next_addSubShiftedRegister_setflags (ms : arm8_state) (op : Bool)
    (rm rn : BitVec 5) (rd : Nat) (hrd : rd ≠ 31) (hlt : rd < 32)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 rd)
          (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
            (if op then ~~~X (TN := 64) rm ms else X (TN := 64) rm ms, op))).1 ms.REG,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (if op then ~~~X (TN := 64) rm ms else X (TN := 64) rm ms, op))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (if op then ~~~X (TN := 64) rm ms else X (TN := 64) rm ms, op))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (if op then ~~~X (TN := 64) rm ms else X (TN := 64) rm ms, op))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (if op then ~~~X (TN := 64) rm ms else X (TN := 64) rm ms, op))).2.2.2.2 } } := by
  let i : instruction := instruction.Data (Data.«AddSubShiftedRegister@64»
    ((1 : BitVec 64), (op, (true, (ShiftType.lsl, (rm, (0, (rn, BitVec.ofNat 5 rd))))))))
  have hdec : Decode (arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd)) = i := by
    dsimp only [i]
    exact arm8Decode_addSubShiftedRegister op true rm 0 rn _
  have hrun := arm8Run_addSubShiftedRegister_setflags_eq op rm rn rd { ms with branch_hint := none } hrd hlt
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd))
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  rfl

/-- One `arm8Next` step on the overflow `ConditionalSelect@64` word: `Rd`
receives `0` when `VC` holds and `1` otherwise, and `PC` advances by four. -/
theorem arm8Next_conditionalSelect_zero (ms : arm8_state) (rd : Nat) (hrd : rd ≠ 31) (hlt : rd < 32)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 rd)
          (if ConditionHolds (7 : BitVec 4) ms then (0 : BitVec 64) else 1) ms.REG,
        PC := ms.PC + 4 } := by
  let i : instruction := instruction.Data (Data.«ConditionalSelect@64»
    ((1 : BitVec 64), (false, (true, ((7 : BitVec 4), ((31 : BitVec 5), ((31 : BitVec 5), BitVec.ofNat 5 rd)))))))
  have hdec : Decode (arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd)) = i := by
    dsimp only [i]
    exact arm8Decode_conditionalSelect _ _ _ _
  let s' : arm8_state := { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 rd) (if ConditionHolds (7 : BitVec 4) ms then (0 : BitVec 64) else 1) ms.REG }
  have hrun : Run i { ms with branch_hint := none } = s' := by
    dsimp only [i, s']
    rw [arm8Run_conditionalSelect_zero]
    rw [arm8WriteX_of_valid _ _ hrd hlt]
    rfl
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd))
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn, hrun]
  dsimp only [s']
  rfl

/-- The encoded bytes of the `addOverflow` lowering: the flag-setting add
followed by the `VC` select. -/
theorem arm8Enc_addOverflow (destination result sourceLeft sourceRight : Nat) :
    arm8Enc (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))) =
      arm8Encode (.Data (.«AddSubShiftedRegister@64»
        (1, false, true, .lsl, BitVec.ofNat 5 sourceLeft, 0,
          BitVec.ofNat 5 result, BitVec.ofNat 5 destination))) ++
      arm8Encode (.Data (.«ConditionalSelect@64»
        (1, false, true, 7, 31, 31, BitVec.ofNat 5 sourceRight))) := by
  rw [arm8Enc]
  simp [arm8Ast]

/-- The encoded bytes of the `subOverflow` lowering: the flag-setting
subtract followed by the `VC` select. -/
theorem arm8Enc_subOverflow (destination result sourceLeft sourceRight : Nat) :
    arm8Enc (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))) =
      arm8Encode (.Data (.«AddSubShiftedRegister@64»
        (1, true, true, .lsl, BitVec.ofNat 5 sourceLeft, 0,
          BitVec.ofNat 5 result, BitVec.ofNat 5 destination))) ++
      arm8Encode (.Data (.«ConditionalSelect@64»
        (1, false, true, 7, 31, 31, BitVec.ofNat 5 sourceRight))) := by
  rw [arm8Enc]
  simp [arm8Ast]

/-- The two-instruction overflow lowerings encode to eight bytes. -/
theorem arm8Enc_addOverflow_length (destination result sourceLeft sourceRight : Nat) :
    (arm8Enc (.inst (.arith (.addOverflow destination result sourceLeft sourceRight)))).length = 8 := by
  rw [arm8Enc_addOverflow]
  simp [arm8Encode_length]

/-- The two-instruction overflow lowerings encode to eight bytes. -/
theorem arm8Enc_subOverflow_length (destination result sourceLeft sourceRight : Nat) :
    (arm8Enc (.inst (.arith (.subOverflow destination result sourceLeft sourceRight)))).length = 8 := by
  rw [arm8Enc_subOverflow]
  simp [arm8Encode_length]

/-- The overflow flag `AddWithCarry` sets for an add: the wrapped sum differs
from the mathematical sum. -/
theorem arm8AddWithCarry_overflow_add (x y : BitVec 64) :
    (AddWithCarry (TN := 64) (x, (y, false))).2.2.2.2 =
      !((x + y).toInt == x.toInt + y.toInt) := by
  simp only [AddWithCarry, Bool.false_eq_true, if_false, Nat.add_zero]
  rw [(BitVec.add_def x y).symm]
  simp

/-- The signed value of the complement plus one is the negation. -/
theorem arm8ToInt_not_add_one (y : BitVec 64) : (~~~y).toInt + 1 = -y.toInt := by
  have hy := y.isLt
  have hcast : ((2 ^ 64 - 1 - y.toNat : ℕ) : ℤ) =
      ((2 ^ 64 : ℕ) : ℤ) - 1 - ((y.toNat : ℕ) : ℤ) := by
    have hle : y.toNat ≤ 2 ^ 64 - 1 := by omega
    omega
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toInt_eq_toNat_bmod, BitVec.toNat_not]
  rw [Int.bmod_def, Int.bmod_def, hcast]
  have h1 : ((((2 ^ 64 : ℕ) : ℤ) - 1 - ((y.toNat : ℕ) : ℤ)) % (((2 ^ 64 : ℕ) : ℤ))) =
      ((2 ^ 64 : ℕ) : ℤ) - 1 - ((y.toNat : ℕ) : ℤ) := by
    apply Int.emod_eq_of_lt <;> omega
  have h2 : ((((y.toNat : ℕ) : ℤ)) % (((2 ^ 64 : ℕ) : ℤ))) = ((y.toNat : ℕ) : ℤ) := by
    apply Int.emod_eq_of_lt <;> omega
  rw [h1, h2]
  split <;> split <;> omega

/-- The overflow flag `AddWithCarry` sets for a subtract: the wrapped
difference differs from the mathematical difference. -/
theorem arm8AddWithCarry_overflow_sub (x y : BitVec 64) :
    (AddWithCarry (TN := 64) (x, (~~~y, true))).2.2.2.2 =
      !((x - y).toInt == x.toInt - y.toInt) := by
  simp only [AddWithCarry, if_true]
  have hres : BitVec.ofNat 64 (x.toNat + (~~~y).toNat + 1) = x - y := by
    rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      ← BitVec.neg_eq_not_add]
  rw [hres]
  congr 2
  have h := arm8ToInt_not_add_one y
  rw [show Int.ofNat 1 = (1 : Int) from rfl]
  omega

end Flapjack.Compiler.Encoders.Arm8.L3