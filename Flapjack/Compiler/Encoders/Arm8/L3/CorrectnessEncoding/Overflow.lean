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

/-- The `VC` select writes `0` when the overflow flag is set, and `1`
otherwise. -/
theorem arm8IteNot (c : Bool) :
    (if (!c) = true then (0 : BitVec 64) else 1) = (if c = true then 1 else 0) := by
  cases c <;> rfl

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

/-- Applying `arm8Next` to two states that agree on `d` and carry the
flag-setting `AddSubShiftedRegister@64` word gives states that still agree. -/
theorem arm8Next_addSubShiftedRegister_setflags_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (op : Bool) (rm rn : BitVec 5) (rd : Nat) (hrd : rd ≠ 31) (hlt : rd < 32)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa [← h.pc] using (holAligned_iff 2 s.PC).mp halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 t.PC).mp halignt
  have hs0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op true ShiftType.lsl rm 0 rn (BitVec.ofNat 5 rd) >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_addSubShiftedRegister_setflags s op rm rn rd hrd hlt hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_addSubShiftedRegister_setflags t op rm rn rd hrd hlt hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hrn : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hrm : X (TN := 64) rm s = X (TN := 64) rm t := arm8X_congr_or_zero h rm
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [h.reg, hrn, hrm]
  · simp only [h.pstate, hrn, hrm]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    simp only [h.mem a ha]

/-- The overflow `ConditionalSelect@64` step leaves memory unchanged. -/
theorem arm8Next_conditionalSelect_zero_mem (ms : arm8_state) (rd : Nat) (hrd : rd ≠ 31) (hlt : rd < 32)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next ms).MEM x = ms.MEM x := by
  rw [arm8Next_conditionalSelect_zero ms rd hrd hlt hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  rfl

/-- Applying `arm8Next` to two states that agree on `d` and carry the overflow
`ConditionalSelect@64` word gives states that still agree. -/
theorem arm8Next_conditionalSelect_zero_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rd : Nat) (hrd : rd ≠ 31) (hlt : rd < 32)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa [← h.pc] using (holAligned_iff 2 s.PC).mp halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 t.PC).mp halignt
  have hs0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalSelectWord false true 7 31 31 (BitVec.ofNat 5 rd) >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_conditionalSelect_zero s rd hrd hlt hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_conditionalSelect_zero t rd hrd hlt hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hcond : ConditionHolds (7 : BitVec 4) s = ConditionHolds (7 : BitVec 4) t := by
    simp only [ConditionHolds, h.pstate]
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [h.reg, hcond]
  · simp only [h.pstate]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    simp only [h.mem a ha]

/-- The `addOverflow` constructor of `encoder_correct arm8TargetL3`: the
flag-setting add followed by the `VC` select simulate the single `addOverflow`
`asmStep` with `n = 1`. -/
theorem arm8_encoder_correct_addOverflow (destination result sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1
      (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hregok : ((asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact result arm8ConfigL3 = true) ∧
      asmRegOkExact sourceLeft arm8ConfigL3 = true) ∧
      asmRegOkExact sourceRight arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3, Bool.and_eq_true] using hk
  obtain ⟨⟨⟨hdl, hdr⟩, hsl⟩, hsr⟩ := hregok
  obtain ⟨hdl_lt, hdl_av, hdl_31⟩ := regOk_of_asmL3 hdl
  obtain ⟨hdr_lt, hdr_av, hdr_31⟩ := regOk_of_asmL3 hdr
  obtain ⟨hsl_lt, hsl_av, hsl_31⟩ := regOk_of_asmL3 hsl
  obtain ⟨hsr_lt, hsr_av, hsr_31⟩ := regOk_of_asmL3 hsr
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  let w0 : BitVec 32 := arm8AddSubShiftedRegisterWord false true ShiftType.lsl
    (BitVec.ofNat 5 sourceLeft) 0 (BitVec.ofNat 5 result) (BitVec.ofNat 5 destination)
  let w1 : BitVec 32 := arm8ConditionalSelectWord false true 7 31 31
    (BitVec.ofNat 5 sourceRight)
  have henc := arm8Enc_addOverflow destination result sourceLeft sourceRight
  have hlen := arm8Enc_addOverflow_length destination result sourceLeft sourceRight
  rw [arm8EncodeBytes_addSubShiftedRegister, arm8EncodeBytes_conditionalSelect] at henc
  have hbyte (i : Nat) (hi : i < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) =
        (arm8Enc (.inst (.arith (.addOverflow destination result sourceLeft sourceRight)))).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [hlen]; exact hi)
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w0 >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w0 >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w0 >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w0 >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 4 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 5 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 6 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 7 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  let ov : Bool := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
    (X (TN := 64) sourceLeft ms, false))).2.2.2.2
  let v1 : BitVec 64 := X (TN := 64) result ms + X (TN := 64) sourceLeft ms
  let T1 : arm8_state :=
    { ms with
      branch_hint := none,
      REG := holUpdate (BitVec.ofNat 5 destination) v1 ms.REG, PC := ms.PC + 4,
      PSTATE := { ms.PSTATE with
        N := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
          (X (TN := 64) sourceLeft ms, false))).2.1,
        Z := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
          (X (TN := 64) sourceLeft ms, false))).2.2.1,
        C := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
          (X (TN := 64) sourceLeft ms, false))).2.2.2.1,
        V := ov } }
  let T2 : arm8_state :=
    { T1 with
      branch_hint := none,
      REG := holUpdate (BitVec.ofNat 5 sourceRight) (if ov then (1 : BitVec 64) else 0) T1.REG,
      PC := T1.PC + 4 }
  have hT1pc : T1.PC = ms.PC + 4 := by rfl
  have hT2pc : T2.PC = ms.PC + 8 := by
    show T1.PC + 4 = ms.PC + 8
    rw [hT1pc, BitVec.add_assoc]
    rfl
  have hT1mem : ∀ x, T1.MEM x = ms.MEM x := by intro x; rfl
  have hT2mem : ∀ x, T2.MEM x = ms.MEM x := by intro x; rfl
  have hT1exc : T1.exception = exception.NoException := hexc0
  have hT1el : T1.PSTATE.EL = (0 : BitVec 2) := hel
  have hT1sctlr : T1.SCTLR_EL1.E0E = false := he0
  have h4 : holAligned 2 (ms.PC + 4) = true := by
    rw [(alignedAddSub 2 ms.PC 4 (by rw [holAligned_iff]; decide)).1]
    exact halign
  have hal4 : Aligned (TN := 64) (T1.PC, 4) = true := by
    rw [hT1pc]
    exact aligned_of_holAligned (ms.PC + 4) h4
  have hn1 : arm8Next ms = T1 := by
    rw [arm8Next_addSubShiftedRegister_setflags ms false (BitVec.ofNat 5 sourceLeft)
      (BitVec.ofNat 5 result) destination hdl_31 hdl_lt hexc0 hb0 hb1 hb2 hb3 hal he0 hel]
    rw [arm8AddWithCarry_add]
    rfl
  have hov : ov = !((X (TN := 64) result ms + X (TN := 64) sourceLeft ms).toInt ==
      (X (TN := 64) result ms).toInt + (X (TN := 64) sourceLeft ms).toInt) :=
    arm8AddWithCarry_overflow_add _ _
  have hb4' : T1.MEM T1.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by rw [hT1mem, hT1pc]; exact hb4
  have hb5' : T1.MEM (T1.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb5
  have hb6' : T1.MEM (T1.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb6
  have hb7' : T1.MEM (T1.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb7
  have hn2 : arm8Next T1 = T2 := by
    rw [arm8Next_conditionalSelect_zero T1 sourceRight hsr_31 hsr_lt hT1exc
      hb4' hb5' hb6' hb7' hal4 hT1sctlr hT1el]
    rw [arm8ConditionHolds_seven]
    have hv : T1.PSTATE.V = ov := rfl
    rw [hv, arm8IteNot ov]
  have hok1 : arm8Ok T1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT1pc]
    exact h4
  have hok2 : arm8Ok T2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT2pc]
    rw [show ms.PC + 8 = ms.PC + 4 + 4 from by rw [BitVec.add_assoc]; rfl,
      (alignedAddSub 2 (ms.PC + 4) 4 (by rw [holAligned_iff]; decide)).1]
    exact h4
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k =
      if k = sourceRight then (if ov then (1 : BitVec 64) else 0)
      else if k = destination then v1 else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, updReg, updPc, Flapjack.Compiler.Encoders.AsmSem.readReg,
      ov, v1, arm8AddWithCarry_overflow_add, arm8X_of_valid, hdr_31, hdr_lt, hsl_31, hsl_lt,
      hreg result ⟨hdr_lt, hdr_av⟩, hreg sourceLeft ⟨hsl_lt, hsl_av⟩]
  have hq : targetStateRel arm8TargetL3 s2 T2 := by
    refine ⟨hok2, ?_, ?_, ?_, ?_⟩
    · change T2.PC = s2.pc
      rw [hT2pc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → T2.MEM a = s2.mem a
      intro a ha
      rw [hT2mem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        T2.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
      rw [hs2regs k]
      unfold T2 T1
      simp only [Flapjack.RiscV.L3.holUpdate]
      by_cases h1 : k = sourceRight
      · rw [if_pos (by rw [h1]), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : k = destination
        · have hne : (BitVec.ofNat 5 sourceRight) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h1 ((arm8Reg_eq hk32 hsr_lt).1 hh.symm)
          rw [if_neg hne, if_pos (by rw [h2]), if_pos h2]
        · have hne1 : (BitVec.ofNat 5 sourceRight) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h1 ((arm8Reg_eq hk32 hsr_lt).1 hh.symm)
          have hne2 : (BitVec.ofNat 5 destination) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h2 ((arm8Reg_eq hk32 hdl_lt).1 hh.symm)
          rw [if_neg hne1, if_neg hne2, if_neg h2]
          exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  have hcode : allPcs 8 s1.pc 0 ⊆ s1.memDomain := by
    have h0' := bytesInMemory_allPcs
      (arm8Enc (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))))
      s1.pc s1.mem s1.memDomain 0 hb
    rw [hlen] at h0'
    exact h0'
  refine ⟨1, ?_⟩
  intro env henv
  dsimp only
  simp only [arm8ConfigL3, hlen]
  have hagree : ∀ k x, Arm8L3Agree s1.memDomain (env k x) x := fun k x => (arm8Proj_eq_iff s1.memDomain _ _).mp (henv k x)
  have a1 : Arm8L3Agree s1.memDomain (env 0 (arm8Next ms)) T1 := by rw [hn1]; exact hagree 0 _
  have hdomT1 : ∀ j, j < 4 → s1.memDomain (T1.PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : T1.PC + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j) := by
      show ms.PC + (4 : BitVec 64) + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j)
      rw [hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom (4 + j) (by omega)
  have huM0 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC) = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    rw [a1.pc, a1.mem T1.PC (by simpa using hdomT1 0 (by omega))]
    exact hb4'
  have huM1 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    rw [a1.pc, a1.mem (T1.PC + 1) (by simpa using hdomT1 1 (by omega))]
    exact hb5'
  have huM2 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    rw [a1.pc, a1.mem (T1.PC + 2) (by simpa using hdomT1 2 (by omega))]
    exact hb6'
  have huM3 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    rw [a1.pc, a1.mem (T1.PC + 3) (by simpa using hdomT1 3 (by omega))]
    exact hb7'
  have huAl : Aligned (TN := 64) ((env 0 (arm8Next ms)).PC, 4) = true := by rw [a1.pc]; exact hal4
  have huExc : (env 0 (arm8Next ms)).exception = exception.NoException := by rw [a1.exc]; exact hexc0
  have a2 : Arm8L3Agree s1.memDomain (arm8Next (env 0 (arm8Next ms))) T2 := by
    have hh := arm8Next_conditionalSelect_zero_agree s1.memDomain (env 0 (arm8Next ms)) T1 a1
      (by rw [arm8Ok_congr a1]; exact hok1) sourceRight hsr_31 hsr_lt
      (by intro j hj; exact hdomT1 j hj) hb4' hb5' hb6' hb7'
    rw [hn2] at hh
    exact hh
  have a2' : Arm8L3Agree s1.memDomain (env 1 (arm8Next (env 0 (arm8Next ms)))) T2 :=
    (hagree 1 (arm8Next (env 0 (arm8Next ms)))).trans a2
  have hu1mem : ∀ x, (arm8Next (env 0 (arm8Next ms))).MEM x = (env 0 (arm8Next ms)).MEM x := by
    intro x
    exact arm8Next_conditionalSelect_zero_mem (env 0 (arm8Next ms)) sourceRight hsr_31 hsr_lt huExc
      huM0 huM1 huM2 huM3 huAl (by rw [a1.sctlr]; exact he0) (by rw [a1.pstate]; exact hel) x
  have hP1 : arm8Ok (env 0 (arm8Next ms)) = true ∧
      (∀ pc, pc ∈ allPcs 8 s1.pc 0 → (env 0 (arm8Next ms)).MEM pc = ms.MEM pc) ∧
      (env 0 (arm8Next ms)).PC ∈ allPcs 8 s1.pc 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [arm8Ok_congr a1]; exact hok1
    · intro pc hpc'
      rw [a1.mem pc (hcode hpc'), hT1mem]
    · rw [a1.pc, hT1pc, hpc]
      simpa using mem_allPcs_eight_l3 s1.pc 1 (by norm_num)
  have hQ : targetStateRel arm8TargetL3 s2 (env 1 (arm8Next (env 0 (arm8Next ms)))) :=
    targetStateRel_congr (hs2dom.symm ▸ a2') hq
  have hP'1 : ∀ x, ¬ s1.memDomain x → ms.MEM x = (arm8Next ms).MEM x := by
    intro x _
    rw [hn1]
  have hP'2 : ∀ x, ¬ s1.memDomain x → (env 0 (arm8Next ms)).MEM x = (arm8Next (env 0 (arm8Next ms))).MEM x := by
    intro x _
    exact (hu1mem x).symm
  constructor
  · simp only [asserts, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP1, hQ⟩
  · simp only [asserts2, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP'1, hP'2, trivial⟩

/-- The `subOverflow` constructor of `encoder_correct arm8TargetL3`: the
flag-setting add followed by the `VC` select simulate the single `subOverflow`
`asmStep` with `n = 1`. -/
theorem arm8_encoder_correct_subOverflow (destination result sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1
      (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hregok : ((asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact result arm8ConfigL3 = true) ∧
      asmRegOkExact sourceLeft arm8ConfigL3 = true) ∧
      asmRegOkExact sourceRight arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3, Bool.and_eq_true] using hk
  obtain ⟨⟨⟨hdl, hdr⟩, hsl⟩, hsr⟩ := hregok
  obtain ⟨hdl_lt, hdl_av, hdl_31⟩ := regOk_of_asmL3 hdl
  obtain ⟨hdr_lt, hdr_av, hdr_31⟩ := regOk_of_asmL3 hdr
  obtain ⟨hsl_lt, hsl_av, hsl_31⟩ := regOk_of_asmL3 hsl
  obtain ⟨hsr_lt, hsr_av, hsr_31⟩ := regOk_of_asmL3 hsr
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  let w0 : BitVec 32 := arm8AddSubShiftedRegisterWord true true ShiftType.lsl
    (BitVec.ofNat 5 sourceLeft) 0 (BitVec.ofNat 5 result) (BitVec.ofNat 5 destination)
  let w1 : BitVec 32 := arm8ConditionalSelectWord false true 7 31 31
    (BitVec.ofNat 5 sourceRight)
  have henc := arm8Enc_subOverflow destination result sourceLeft sourceRight
  have hlen := arm8Enc_subOverflow_length destination result sourceLeft sourceRight
  rw [arm8EncodeBytes_addSubShiftedRegister, arm8EncodeBytes_conditionalSelect] at henc
  have hbyte (i : Nat) (hi : i < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) =
        (arm8Enc (.inst (.arith (.subOverflow destination result sourceLeft sourceRight)))).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [hlen]; exact hi)
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w0 >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w0 >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w0 >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w0 >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 4 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 5 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 6 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 7 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  let ov : Bool := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
    (~~~X (TN := 64) sourceLeft ms, true))).2.2.2.2
  let v1 : BitVec 64 := X (TN := 64) result ms - X (TN := 64) sourceLeft ms
  let T1 : arm8_state :=
    { ms with
      branch_hint := none,
      REG := holUpdate (BitVec.ofNat 5 destination) v1 ms.REG, PC := ms.PC + 4,
      PSTATE := { ms.PSTATE with
        N := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
          (~~~X (TN := 64) sourceLeft ms, true))).2.1,
        Z := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
          (~~~X (TN := 64) sourceLeft ms, true))).2.2.1,
        C := (AddWithCarry (TN := 64) (X (TN := 64) result ms,
          (~~~X (TN := 64) sourceLeft ms, true))).2.2.2.1,
        V := ov } }
  let T2 : arm8_state :=
    { T1 with
      branch_hint := none,
      REG := holUpdate (BitVec.ofNat 5 sourceRight) (if ov then (1 : BitVec 64) else 0) T1.REG,
      PC := T1.PC + 4 }
  have hT1pc : T1.PC = ms.PC + 4 := by rfl
  have hT2pc : T2.PC = ms.PC + 8 := by
    show T1.PC + 4 = ms.PC + 8
    rw [hT1pc, BitVec.add_assoc]
    rfl
  have hT1mem : ∀ x, T1.MEM x = ms.MEM x := by intro x; rfl
  have hT2mem : ∀ x, T2.MEM x = ms.MEM x := by intro x; rfl
  have hT1exc : T1.exception = exception.NoException := hexc0
  have hT1el : T1.PSTATE.EL = (0 : BitVec 2) := hel
  have hT1sctlr : T1.SCTLR_EL1.E0E = false := he0
  have h4 : holAligned 2 (ms.PC + 4) = true := by
    rw [(alignedAddSub 2 ms.PC 4 (by rw [holAligned_iff]; decide)).1]
    exact halign
  have hal4 : Aligned (TN := 64) (T1.PC, 4) = true := by
    rw [hT1pc]
    exact aligned_of_holAligned (ms.PC + 4) h4
  have hn1 : arm8Next ms = T1 := by
    rw [arm8Next_addSubShiftedRegister_setflags ms true (BitVec.ofNat 5 sourceLeft)
      (BitVec.ofNat 5 result) destination hdl_31 hdl_lt hexc0 hb0 hb1 hb2 hb3 hal he0 hel]
    simp only [if_true, arm8AddWithCarry_sub]
    rfl
  have hov : ov = !((X (TN := 64) result ms - X (TN := 64) sourceLeft ms).toInt ==
      (X (TN := 64) result ms).toInt - (X (TN := 64) sourceLeft ms).toInt) :=
    arm8AddWithCarry_overflow_sub _ _
  have hb4' : T1.MEM T1.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by rw [hT1mem, hT1pc]; exact hb4
  have hb5' : T1.MEM (T1.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb5
  have hb6' : T1.MEM (T1.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb6
  have hb7' : T1.MEM (T1.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb7
  have hn2 : arm8Next T1 = T2 := by
    rw [arm8Next_conditionalSelect_zero T1 sourceRight hsr_31 hsr_lt hT1exc
      hb4' hb5' hb6' hb7' hal4 hT1sctlr hT1el]
    rw [arm8ConditionHolds_seven]
    have hv : T1.PSTATE.V = ov := rfl
    rw [hv, arm8IteNot ov]
  have hok1 : arm8Ok T1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT1pc]
    exact h4
  have hok2 : arm8Ok T2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT2pc]
    rw [show ms.PC + 8 = ms.PC + 4 + 4 from by rw [BitVec.add_assoc]; rfl,
      (alignedAddSub 2 (ms.PC + 4) 4 (by rw [holAligned_iff]; decide)).1]
    exact h4
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k =
      if k = sourceRight then (if ov then (1 : BitVec 64) else 0)
      else if k = destination then v1 else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, updReg, updPc, Flapjack.Compiler.Encoders.AsmSem.readReg,
      ov, v1, arm8AddWithCarry_overflow_sub, arm8X_of_valid, hdr_31, hdr_lt, hsl_31, hsl_lt,
      hreg result ⟨hdr_lt, hdr_av⟩, hreg sourceLeft ⟨hsl_lt, hsl_av⟩]
  have hq : targetStateRel arm8TargetL3 s2 T2 := by
    refine ⟨hok2, ?_, ?_, ?_, ?_⟩
    · change T2.PC = s2.pc
      rw [hT2pc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → T2.MEM a = s2.mem a
      intro a ha
      rw [hT2mem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        T2.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
      rw [hs2regs k]
      unfold T2 T1
      simp only [Flapjack.RiscV.L3.holUpdate]
      by_cases h1 : k = sourceRight
      · rw [if_pos (by rw [h1]), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : k = destination
        · have hne : (BitVec.ofNat 5 sourceRight) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h1 ((arm8Reg_eq hk32 hsr_lt).1 hh.symm)
          rw [if_neg hne, if_pos (by rw [h2]), if_pos h2]
        · have hne1 : (BitVec.ofNat 5 sourceRight) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h1 ((arm8Reg_eq hk32 hsr_lt).1 hh.symm)
          have hne2 : (BitVec.ofNat 5 destination) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h2 ((arm8Reg_eq hk32 hdl_lt).1 hh.symm)
          rw [if_neg hne1, if_neg hne2, if_neg h2]
          exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  have hcode : allPcs 8 s1.pc 0 ⊆ s1.memDomain := by
    have h0' := bytesInMemory_allPcs
      (arm8Enc (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))))
      s1.pc s1.mem s1.memDomain 0 hb
    rw [hlen] at h0'
    exact h0'
  refine ⟨1, ?_⟩
  intro env henv
  dsimp only
  simp only [arm8ConfigL3, hlen]
  have hagree : ∀ k x, Arm8L3Agree s1.memDomain (env k x) x := fun k x => (arm8Proj_eq_iff s1.memDomain _ _).mp (henv k x)
  have a1 : Arm8L3Agree s1.memDomain (env 0 (arm8Next ms)) T1 := by rw [hn1]; exact hagree 0 _
  have hdomT1 : ∀ j, j < 4 → s1.memDomain (T1.PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : T1.PC + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j) := by
      show ms.PC + (4 : BitVec 64) + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j)
      rw [hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom (4 + j) (by omega)
  have huM0 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC) = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    rw [a1.pc, a1.mem T1.PC (by simpa using hdomT1 0 (by omega))]
    exact hb4'
  have huM1 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    rw [a1.pc, a1.mem (T1.PC + 1) (by simpa using hdomT1 1 (by omega))]
    exact hb5'
  have huM2 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    rw [a1.pc, a1.mem (T1.PC + 2) (by simpa using hdomT1 2 (by omega))]
    exact hb6'
  have huM3 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    rw [a1.pc, a1.mem (T1.PC + 3) (by simpa using hdomT1 3 (by omega))]
    exact hb7'
  have huAl : Aligned (TN := 64) ((env 0 (arm8Next ms)).PC, 4) = true := by rw [a1.pc]; exact hal4
  have huExc : (env 0 (arm8Next ms)).exception = exception.NoException := by rw [a1.exc]; exact hexc0
  have a2 : Arm8L3Agree s1.memDomain (arm8Next (env 0 (arm8Next ms))) T2 := by
    have hh := arm8Next_conditionalSelect_zero_agree s1.memDomain (env 0 (arm8Next ms)) T1 a1
      (by rw [arm8Ok_congr a1]; exact hok1) sourceRight hsr_31 hsr_lt
      (by intro j hj; exact hdomT1 j hj) hb4' hb5' hb6' hb7'
    rw [hn2] at hh
    exact hh
  have a2' : Arm8L3Agree s1.memDomain (env 1 (arm8Next (env 0 (arm8Next ms)))) T2 :=
    (hagree 1 (arm8Next (env 0 (arm8Next ms)))).trans a2
  have hu1mem : ∀ x, (arm8Next (env 0 (arm8Next ms))).MEM x = (env 0 (arm8Next ms)).MEM x := by
    intro x
    exact arm8Next_conditionalSelect_zero_mem (env 0 (arm8Next ms)) sourceRight hsr_31 hsr_lt huExc
      huM0 huM1 huM2 huM3 huAl (by rw [a1.sctlr]; exact he0) (by rw [a1.pstate]; exact hel) x
  have hP1 : arm8Ok (env 0 (arm8Next ms)) = true ∧
      (∀ pc, pc ∈ allPcs 8 s1.pc 0 → (env 0 (arm8Next ms)).MEM pc = ms.MEM pc) ∧
      (env 0 (arm8Next ms)).PC ∈ allPcs 8 s1.pc 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [arm8Ok_congr a1]; exact hok1
    · intro pc hpc'
      rw [a1.mem pc (hcode hpc'), hT1mem]
    · rw [a1.pc, hT1pc, hpc]
      simpa using mem_allPcs_eight_l3 s1.pc 1 (by norm_num)
  have hQ : targetStateRel arm8TargetL3 s2 (env 1 (arm8Next (env 0 (arm8Next ms)))) :=
    targetStateRel_congr (hs2dom.symm ▸ a2') hq
  have hP'1 : ∀ x, ¬ s1.memDomain x → ms.MEM x = (arm8Next ms).MEM x := by
    intro x _
    rw [hn1]
  have hP'2 : ∀ x, ¬ s1.memDomain x → (env 0 (arm8Next ms)).MEM x = (arm8Next (env 0 (arm8Next ms))).MEM x := by
    intro x _
    exact (hu1mem x).symm
  constructor
  · simp only [asserts, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP1, hQ⟩
  · simp only [asserts2, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP'1, hP'2, trivial⟩

end Flapjack.Compiler.Encoders.Arm8.L3