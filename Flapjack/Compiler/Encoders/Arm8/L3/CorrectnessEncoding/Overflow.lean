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

/-- The `addOverflow` constructor of `encoder_correct arm8TargetL3`: the
flag-setting add followed by the `VC` select simulate the single `addOverflow`
`asmStep` with `n = 1`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_addOverflow (destination result sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1
      (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))) s1 s2 ms := by
  have hs := h.1
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
  refine arm8RegCaseTwo _ s1 s2 ms h
    (.Data (.«AddSubShiftedRegister@64» (1, false, true, .lsl, BitVec.ofNat 5 sourceLeft, 0,
      BitVec.ofNat 5 result, BitVec.ofNat 5 destination))) _
    (.Data (.«ConditionalSelect@64» (1, false, true, 7, 31, 31, BitVec.ofNat 5 sourceRight))) _ _ _
    T1.REG T2.REG T1.PSTATE
    (arm8Enc_addOverflow destination result sourceLeft sourceRight)
    (arm8Encode_addSubShiftedRegister _ _ _ _ _ _ _) (arm8Decode_addSubShiftedRegister false true _ 0 _ _)
    (arm8Encode_conditionalSelect _ _ _ _ _ _) (arm8Decode_conditionalSelect _ _ _ _) ?_ rfl ?_ ?_
  · intro _
    rw [arm8Run_addSubShiftedRegister_setflags_eq false _ _ destination _ hdl_31 hdl_lt]
    rw [arm8AddWithCarry_add]
    rfl
  · intro u hR hP
    rw [arm8Run_conditionalSelect_zero, arm8WriteX_of_valid _ _ hsr_31 hsr_lt, arm8ConditionHolds_seven]
    dsimp only
    rw [hR, hP]
    have hv : T1.PSTATE.V = ov := rfl
    rw [hv, arm8IteNot ov]
  · intro hreg p
    refine ⟨by simp [asmUpd, instUpd, arithUpd, updPc], fun x => by
      simp [asmUpd, instUpd, arithUpd, updReg, updPc], by simp [asmUpd, instUpd, arithUpd, updReg, updPc],
      fun k hk32 hav => ?_⟩
    have hp : ∀ k, (asmUpd (.inst (.arith (.addOverflow destination result sourceLeft sourceRight))) p s1).regs k =
        if k = sourceRight then (if ov then (1 : BitVec 64) else 0)
      else if k = destination then v1 else s1.regs k := by
      intro k
      simp [asmUpd, instUpd, arithUpd, updReg, updPc, Flapjack.Compiler.Encoders.AsmSem.readReg,
        ov, v1, arm8AddWithCarry_overflow_add, arm8X_of_valid, hdr_31, hdr_lt, hsl_31, hsl_lt,
        hreg result ⟨hdr_lt, hdr_av⟩, hreg sourceLeft ⟨hsl_lt, hsl_av⟩]
    show T2.REG (BitVec.ofNat 5 k) = _
    rw [hp k]
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
        exact hreg k ⟨hk32, hav⟩

/-- The `subOverflow` constructor of `encoder_correct arm8TargetL3`: the
flag-setting add followed by the `VC` select simulate the single `subOverflow`
`asmStep` with `n = 1`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_subOverflow (destination result sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1
      (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))) s1 s2 ms := by
  have hs := h.1
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
  refine arm8RegCaseTwo _ s1 s2 ms h
    (.Data (.«AddSubShiftedRegister@64» (1, true, true, .lsl, BitVec.ofNat 5 sourceLeft, 0,
      BitVec.ofNat 5 result, BitVec.ofNat 5 destination))) _
    (.Data (.«ConditionalSelect@64» (1, false, true, 7, 31, 31, BitVec.ofNat 5 sourceRight))) _ _ _
    T1.REG T2.REG T1.PSTATE
    (arm8Enc_subOverflow destination result sourceLeft sourceRight)
    (arm8Encode_addSubShiftedRegister _ _ _ _ _ _ _) (arm8Decode_addSubShiftedRegister true true _ 0 _ _)
    (arm8Encode_conditionalSelect _ _ _ _ _ _) (arm8Decode_conditionalSelect _ _ _ _) ?_ rfl ?_ ?_
  · intro _
    rw [arm8Run_addSubShiftedRegister_setflags_eq true _ _ destination _ hdl_31 hdl_lt]
    simp only [if_true, arm8AddWithCarry_sub]
    rfl
  · intro u hR hP
    rw [arm8Run_conditionalSelect_zero, arm8WriteX_of_valid _ _ hsr_31 hsr_lt, arm8ConditionHolds_seven]
    dsimp only
    rw [hR, hP]
    have hv : T1.PSTATE.V = ov := rfl
    rw [hv, arm8IteNot ov]
  · intro hreg p
    refine ⟨by simp [asmUpd, instUpd, arithUpd, updPc], fun x => by
      simp [asmUpd, instUpd, arithUpd, updReg, updPc], by simp [asmUpd, instUpd, arithUpd, updReg, updPc],
      fun k hk32 hav => ?_⟩
    have hp : ∀ k, (asmUpd (.inst (.arith (.subOverflow destination result sourceLeft sourceRight))) p s1).regs k =
        if k = sourceRight then (if ov then (1 : BitVec 64) else 0)
      else if k = destination then v1 else s1.regs k := by
      intro k
      simp [asmUpd, instUpd, arithUpd, updReg, updPc, Flapjack.Compiler.Encoders.AsmSem.readReg,
        ov, v1, arm8AddWithCarry_overflow_sub, arm8X_of_valid, hdr_31, hdr_lt, hsl_31, hsl_lt,
        hreg result ⟨hdr_lt, hdr_av⟩, hreg sourceLeft ⟨hsl_lt, hsl_av⟩]
    show T2.REG (BitVec.ofNat 5 k) = _
    rw [hp k]
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
        exact hreg k ⟨hk32, hav⟩

end Flapjack.Compiler.Encoders.Arm8.L3
