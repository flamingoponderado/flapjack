import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Compare
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.JumpCmp
import Flapjack.Compiler.Encoders.Arm8.Machine.MulCarryCase

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `addCarry`

`arm8_ast` lowers `AddCarry r1 r2 r3 r4` to five instructions: a flag-setting
`SUBS XZR, r4, #0`, a `ConditionalCompareImmediate@64` on `r2` against zero
under the `EQ` condition, an `AddSubCarry@64` into `r1`, a `MoveWide .z` that
zeroes `r4`, and a final `AddSubCarry@64` into `r4`.  This module records the
step lemmas, the byte lists and the agreement facts, then assembles the case.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The unsigned comparison with zero is false. -/
theorem arm8Ult_zero (x : BitVec 64) : x.ult (0 : BitVec 64) = false := by
  show decide (x.toNat < (0 : BitVec 64).toNat) = false
  simp

/-- `BitVec.msb` at 64 bits is the top bit. -/
theorem arm8Msb_eq_getLsbD (x : BitVec 64) : BitVec.msb x = x.getLsbD 63 := by
  rw [BitVec.msb, arm8GetMsbD_zero_64]

/-- The rendered `Decode` inverts `arm8AddSubCarryWord` for both `opc`/`s`
combinations. -/
theorem arm8Decode_addSubCarry_gen (opc s : Bool) (rm rn rd : BitVec 5) :
    Decode (arm8AddSubCarryWord opc s rm rn rd) =
      instruction.Data (Data.«AddSubCarry@64»
        ((1 : BitVec 64), (opc, (s, (rm, (rn, rd)))))) := by
  simp only [arm8AddSubCarryWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases opc <;> cases s <;> simp [holV2w_one_false, holV2w_one_true, holV2w_five]

/-- `AddWithCarry` of `x` with the complemented zero is `x` with the flags of
`x - 0`. -/
theorem arm8AddWithCarry_subs_zero (x : BitVec 64) :
    AddWithCarry (TN := 64) (x, (~~~(0 : BitVec 64), true)) =
      (x, (BitVec.msb x, ((x == (0 : BitVec 64)), (true, false)))) := by
  rw [arm8AddWithCarry_machine, addWithCarry_subFlags]
  simp only [subFlags]
  have hx : x - (0 : BitVec 64) = x := by simp
  have hC : decide (x.toNat ≠ x.toNat + (~~~(0 : BitVec 64)).toNat + 1) = true := by
    have h : (~~~(0 : BitVec 64)).toNat = 2 ^ 64 - 1 := by decide
    rw [h, decide_eq_true_iff]
    omega
  have hV : decide (x.toInt ≠ x.toInt + (~~~(0 : BitVec 64)).toInt + 1) = false := by
    have h : (~~~(0 : BitVec 64)).toInt = -1 := by decide
    rw [h, decide_eq_false_iff_not]
    omega
  rw [hx, hC, hV, arm8Msb_eq_getLsbD]
  rw [← arm8Beq_eq_decide x 0]

/-- `AddWithCarry` of `x` with the zero immediate and no carry is `x` with the
flags of `x + 0`. -/
theorem arm8AddWithCarry_add_zero (x : BitVec 64) :
    AddWithCarry (TN := 64) (x, ((0 : BitVec 64), false)) =
      (x, (BitVec.msb x, ((x == (0 : BitVec 64)), (false, false)))) := by
  rw [arm8AddWithCarry_machine, addWithCarry_addFlags]
  simp only [addFlags]
  have hx : x + (0 : BitVec 64) = x := by simp
  have hC : decide (x.toNat ≠ x.toNat + (0 : BitVec 64).toNat) = false := by
    have h : (0 : BitVec 64).toNat = 0 := by decide
    rw [h, decide_eq_false_iff_not]
    omega
  have hV : decide (x.toInt ≠ x.toInt + (0 : BitVec 64).toInt) = false := by
    have h : (0 : BitVec 64).toInt = 0 := by decide
    rw [h, decide_eq_false_iff_not]
    omega
  rw [hx, hC, hV, arm8Msb_eq_getLsbD]
  rw [← arm8Beq_eq_decide x 0]

/-- One `arm8Next` step on the `SUBS XZR, rn, #0` compare that starts the
`addCarry` lowering. -/
theorem arm8Next_addSubImmediateS_zero (ms : arm8_state) (rn : BitVec 5)
    (hrn : rn ≠ 31)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := BitVec.msb (X (TN := 64) rn ms),
            Z := (X (TN := 64) rn ms) == (0 : BitVec 64),
            C := true,
            V := false } } := by
  have hlow : (0 : BitVec 64) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by decide
  have hn := arm8Next_addSubImmediateS_low ms 0 rn hlow hrn hexc0 h0 h1 h2 h3 hal he0 hel
  rw [hn, arm8AddWithCarry_subs_zero]

/-- One `arm8Next` step on the `MoveWide .z` instruction that zeroes a register
in the `addCarry` lowering. -/
theorem arm8Next_moveWide_z_zero (ms : arm8_state) (rd : BitVec 5)
    (hrd : rd ≠ 31)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        REG := holUpdate rd (0 : BitVec 64) ms.REG } := by
  let i : instruction := instruction.Data (Data.«MoveWide@64»
    ((1 : BitVec 64), (.z, ((0 : BitVec 2), ((0 : BitVec 16), rd)))))
  have hdec : Decode (arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd) = i := by
    dsimp only [i]
    exact arm8Decode_moveWide .z (0 : BitVec 2) (0 : BitVec 16) rd
  have hrun := arm8Run_moveWide_z (0 : BitVec 2) (0 : BitVec 16) rd
    { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun, if_neg hrd]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun, if_neg hrd]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd)
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun, if_neg hrd]
  rfl

/-! ## Projections through `SetTheFlags` and `write'X` -/

theorem setTheFlags_branchHint (b : Bool) (n z c v : Bool) (s : arm8_state) :
    (SetTheFlags (b, (n, (z, (c, v)))) s).branch_hint = s.branch_hint := by
  simp only [SetTheFlags]; split <;> rfl

theorem setTheFlags_exception (b : Bool) (n z c v : Bool) (s : arm8_state) :
    (SetTheFlags (b, (n, (z, (c, v)))) s).exception = s.exception := by
  simp only [SetTheFlags]; split <;> rfl

theorem setTheFlags_mem (b : Bool) (n z c v : Bool) (s : arm8_state) :
    (SetTheFlags (b, (n, (z, (c, v)))) s).MEM = s.MEM := by
  simp only [SetTheFlags]; split <;> rfl

theorem setTheFlags_reg (b : Bool) (n z c v : Bool) (s : arm8_state) :
    (SetTheFlags (b, (n, (z, (c, v)))) s).REG = s.REG := by
  simp only [SetTheFlags]; split <;> rfl

theorem arm8X_branchHint (n : BitVec 5) (s : arm8_state) :
    X (TN := 64) n { s with branch_hint := none } = X (TN := 64) n s := rfl

theorem conditionHolds_branchHint (cd : BitVec 4) (s : arm8_state) :
    ConditionHolds cd { s with branch_hint := none } = ConditionHolds cd s := rfl

theorem setTheFlags_eq (b : Bool) (flags : Bool × (Bool × (Bool × Bool)))
    (s : arm8_state) :
    SetTheFlags (b, flags) s =
      if b then
        { s with
          PSTATE :=
            { s.PSTATE with
              N := flags.1,
              Z := flags.2.1,
              C := flags.2.2.1,
              V := flags.2.2.2 } }
      else s := by
  obtain ⟨n, z, c, v⟩ := flags
  simp only [SetTheFlags]

theorem writeX_branchHint (v : BitVec 64) (n : BitVec 5) (s : arm8_state) :
    («write'X» (v, n) s).branch_hint = s.branch_hint := by
  simp only [«write'X»]; split <;> rfl

theorem writeX_exception (v : BitVec 64) (n : BitVec 5) (s : arm8_state) :
    («write'X» (v, n) s).exception = s.exception := by
  simp only [«write'X»]; split <;> rfl

theorem writeX_mem (v : BitVec 64) (n : BitVec 5) (s : arm8_state) :
    («write'X» (v, n) s).MEM = s.MEM := by
  simp only [«write'X»]; split <;> rfl

/-- The `AddWithCarry` zero-compare equation in the `BitVec.ofNat` form the
rendered instruction produces. -/
theorem arm8AddWithCarry_add_zero_ofNat (x : BitVec 64) :
    AddWithCarry (TN := 64) (x, (BitVec.ofNat 64 0, false)) =
      (x, (BitVec.msb x, ((x == BitVec.ofNat 64 0), (false, false)))) :=
  arm8AddWithCarry_add_zero x

/-- `Run` of the `ConditionalCompareImmediate@64` that follows the zero compare
in the `addCarry` lowering. -/
theorem arm8Run_conditionalCompare_zero (rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«ConditionalCompareImmediate@64»
      ((1 : BitVec 64), (false, ((0 : BitVec 64), ((0 : BitVec 4),
        ((false, (false, (true, false))), rn))))))) st =
      if ConditionHolds (0 : BitVec 4) st then
        SetTheFlags (true, (AddWithCarry (TN := 64) (X (TN := 64) rn st,
          ((0 : BitVec 64), false))).2) st
      else SetTheFlags (true, (false, (false, (true, false)))) st := by
  rw [arm8Run_conditionalCompare]
  simp only [Bool.false_eq_true, if_false]

/-- One `arm8Next` step on the `ConditionalCompareImmediate@64` that follows the
zero compare in the `addCarry` lowering: compare `rn` with zero under `EQ`, or
set the literal `nzcv` when `EQ` does not hold. -/
theorem arm8Next_conditionalCompare_zero (ms : arm8_state) (rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      if ConditionHolds (0 : BitVec 4) { ms with branch_hint := none } then
        { ms with
          branch_hint := none,
          PC := ms.PC + 4,
          PSTATE :=
            { ms.PSTATE with
              N := BitVec.msb (X (TN := 64) rn { ms with branch_hint := none }),
              Z := (X (TN := 64) rn { ms with branch_hint := none }) == (0 : BitVec 64),
              C := false,
              V := false } }
      else
        { ms with
          branch_hint := none,
          PC := ms.PC + 4,
          PSTATE :=
            { ms.PSTATE with N := false, Z := false, C := true, V := false } } := by
  let i : instruction := instruction.Data (Data.«ConditionalCompareImmediate@64»
    ((1 : BitVec 64), (false, ((0 : BitVec 64), ((0 : BitVec 4),
      ((false, (false, (true, false))), rn))))))
  have himm : ((0 : BitVec 64) == BitVec.setWidth 64 (BitVec.setWidth 5
      (0 : BitVec 64))) = true := by
    rw [beq_iff_eq]; simp
  have henc : Encode (.Data (.«ConditionalCompareImmediate@64»
      ((1 : BitVec 64), (false, ((0 : BitVec 64), ((0 : BitVec 4),
        ((false, (false, (true, false))), rn))))))) =
      MachineCode.ARM8 (arm8ConditionalCompareWord false (0 : BitVec 5)
        (0 : BitVec 4) false false true false rn) := by
    rw [arm8Encode_conditionalCompare, if_pos himm]
    simp
  have hdec : Decode (arm8ConditionalCompareWord false (0 : BitVec 5)
      (0 : BitVec 4) false false true false rn) = i := by
    dsimp only [i]
    exact arm8Decode_conditionalCompare (0 : BitVec 5) (0 : BitVec 4) rn
  have hrun := arm8Run_conditionalCompare_zero rn { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
    split
    · rw [setTheFlags_branchHint]
    · rw [setTheFlags_branchHint]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    split
    · rw [setTheFlags_exception]; simpa using hexc0
    · rw [setTheFlags_exception]; simpa using hexc0
  have hn := arm8Next_word ms (arm8ConditionalCompareWord false (0 : BitVec 5)
    (0 : BitVec 4) false false true false rn) i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  simp only [holThe, setTheFlags_eq]
  split
  · simp [arm8AddWithCarry_add_zero_ofNat]
  · simp

theorem arm8Run_addSubCarry_eq (s : Bool) (rm rn rd : BitVec 5) (st : arm8_state)
    (hrd : rd ≠ 31) :
    Run (instruction.Data (Data.«AddSubCarry@64»
      ((1 : BitVec 64), (false, (s, (rm, (rn, rd))))))) st =
      (SetTheFlags (s, (AddWithCarry (TN := 64) (X (TN := 64) rn st,
        (X (TN := 64) rm st, st.PSTATE.C))).2)
        { st with REG := holUpdate rd (AddWithCarry (TN := 64) (X (TN := 64) rn st,
          (X (TN := 64) rm st, st.PSTATE.C))).1 st.REG }) := by
  rw [arm8Run_addSubCarry]
  simp only [«write'X», Bool.false_eq_true, if_false]
  have hbeq : (rd == BitVec.ofNat 5 31) = false := beq_eq_false_iff_ne.mpr hrd
  simp only [hbeq, Bool.not_false, if_true]
  simp only [setTheFlags_eq]
  split <;> simp

theorem arm8Next_addSubCarry (ms : arm8_state) (s : Bool) (rm rn rd : BitVec 5)
    (hrd : rd ≠ 31)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddSubCarryWord false s rm rn rd >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddSubCarryWord false s rm rn rd >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddSubCarryWord false s rm rn rd >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddSubCarryWord false s rm rn rd >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        REG := holUpdate rd (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
          (X (TN := 64) rm ms, ms.PSTATE.C))).1 ms.REG,
        PSTATE :=
          (SetTheFlags (s, (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
            (X (TN := 64) rm ms, ms.PSTATE.C))).2) ms).PSTATE } := by
  let i : instruction := instruction.Data (Data.«AddSubCarry@64»
    ((1 : BitVec 64), (false, (s, (rm, (rn, rd))))))
  have hdec : Decode (arm8AddSubCarryWord false s rm rn rd) = i := by
    dsimp only [i]
    exact arm8Decode_addSubCarry_gen false s rm rn rd
  have hrun := arm8Run_addSubCarry_eq s rm rn rd { ms with branch_hint := none } hrd
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
    simp only [SetTheFlags]
    split <;> rfl
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simp only [SetTheFlags]
    split <;> simpa using hexc0
  have hn := arm8Next_word ms (arm8AddSubCarryWord false s rm rn rd) i hdec hbr hexc
    h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  simp only [holThe, setTheFlags_eq]
  split <;> simp [arm8X_branchHint]

/-- `SetTheFlags` preserves the `PSTATE` agreement of two states. -/
theorem setTheFlags_pstate_congr (b : Bool) (flags : Bool × (Bool × (Bool × Bool)))
    (s t : arm8_state) (h : s.PSTATE = t.PSTATE) :
    (SetTheFlags (b, flags) s).PSTATE = (SetTheFlags (b, flags) t).PSTATE := by
  by_cases hb : b = true <;> simp [setTheFlags_eq, hb, h]

/-- The `SUBS XZR, rn, #0` step preserves agreement. -/
theorem arm8Next_addSubImmediateS_zero_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rn : BitVec 5) (hrn : rn ≠ 31)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) rn 31 >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := aligned_of_holAligned s.PC halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := aligned_of_holAligned t.PC halignt
  have hs0 := (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 := (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 := (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 := (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  rw [← h.pc] at hs0 hs1 hs2 hs3
  have hss := arm8Next_addSubImmediateS_zero s rn hrn hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_addSubImmediateS_zero t rn hrn hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hx : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · exact h.reg
  · simp only [h.pstate, hx]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    exact h.mem a ha

/-- The `ConditionalCompareImmediate@64` zero compare preserves agreement. -/
theorem arm8Next_conditionalCompare_zero_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rn : BitVec 5)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false
      (0 : BitVec 5) (0 : BitVec 4) false false true false rn >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := aligned_of_holAligned s.PC halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := aligned_of_holAligned t.PC halignt
  have hs0 := (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 := (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 := (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 := (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  rw [← h.pc] at hs0 hs1 hs2 hs3
  have hss := arm8Next_conditionalCompare_zero s rn hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_conditionalCompare_zero t rn hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hx : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hcd : ConditionHolds (0 : BitVec 4) { s with branch_hint := none } =
      ConditionHolds (0 : BitVec 4) { t with branch_hint := none } :=
    arm8ConditionHolds_congr (0 : BitVec 4) (by rw [h.pstate])
  rw [hss, htt, hcd]
  split_ifs with hc
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h.pc]
    · exact h.reg
    · have hX : X (TN := 64) rn { s with branch_hint := none } =
          X (TN := 64) rn { t with branch_hint := none } := by
        rw [show X (TN := 64) rn { s with branch_hint := none } = X (TN := 64) rn s from rfl,
          show X (TN := 64) rn { t with branch_hint := none } = X (TN := 64) rn t from rfl, hx]
      rw [hX, h.pstate]
    · simp [h.sctlr]
    · simp [h.tcr]
    · simp [h.exc]
    · intro a ha
      exact h.mem a ha
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h.pc]
    · exact h.reg
    · simp [h.pstate]
    · simp [h.sctlr]
    · simp [h.tcr]
    · simp [h.exc]
    · intro a ha
      exact h.mem a ha

/-- The `AddSubCarry@64` step preserves agreement. -/
theorem arm8Next_addSubCarry_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (sb : Bool) (rm rn rd : BitVec 5) (hrd : rd ≠ 31)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := aligned_of_holAligned s.PC halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := aligned_of_holAligned t.PC halignt
  have hs0 := (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 := (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 := (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 := (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  rw [← h.pc] at hs0 hs1 hs2 hs3
  have hss := arm8Next_addSubCarry s sb rm rn rd hrd hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_addSubCarry t sb rm rn rd hrd hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hx : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hxm : X (TN := 64) rm s = X (TN := 64) rm t := arm8X_congr_or_zero h rm
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [h.reg, hx, hxm, h.pstate]
  · simp only [setTheFlags_pstate_congr sb _ _ _ h.pstate, h.pstate, hx, hxm]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    exact h.mem a ha

/-- The `MoveWide .z` zeroing step preserves agreement. -/
theorem arm8Next_moveWide_z_zero_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rd : BitVec 5) (hrd : rd ≠ 31)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2)
      (0 : BitVec 16) rd >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := aligned_of_holAligned s.PC halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := aligned_of_holAligned t.PC halignt
  have hs0 := (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 := (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 := (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 := (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  rw [← h.pc] at hs0 hs1 hs2 hs3
  have hss := arm8Next_moveWide_z_zero s rd hrd hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_moveWide_z_zero t rd hrd hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp [h.reg]
  · simp [h.pstate]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    exact h.mem a ha

/-- The four encoded bytes of the `CCMI rn, #0` word. -/
theorem arm8EncodeBytes_conditionalCompare (rn : BitVec 5) :
    arm8Encode (.Data (.«ConditionalCompareImmediate@64»
      ((1 : BitVec 64), (false, ((0 : BitVec 64), ((0 : BitVec 4),
        ((false, (false, (true, false))), rn))))))) =
      [BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
          false false true false rn >>> 0).toNat),
       BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
          false false true false rn >>> 8).toNat),
       BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
          false false true false rn >>> 16).toNat),
       BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
          false false true false rn >>> 24).toNat)] := by
  have himm : ((0 : BitVec 64) == BitVec.setWidth 64 (BitVec.setWidth 5
      (0 : BitVec 64))) = true := by
    rw [beq_iff_eq]; simp
  rw [arm8Encode, arm8Encode_conditionalCompare, if_pos himm]
  simp

/-- The four encoded bytes of an `AddSubCarry@64` word. -/
theorem arm8EncodeBytes_addSubCarry (sb : Bool) (rm rn rd : BitVec 5) :
    arm8Encode (.Data (.«AddSubCarry@64»
      ((1 : BitVec 64), (false, (sb, (rm, (rn, rd))))))) =
      [BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_addSubCarry]

/-- The four encoded bytes of a `MOVZ rd, #0` word. -/
theorem arm8EncodeBytes_moveWide_z_zero (rd : BitVec 5) :
    arm8Encode (.Data (.«MoveWide@64»
      ((1 : BitVec 64), (.z, ((0 : BitVec 2), ((0 : BitVec 16), rd)))))) =
      [BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_moveWide]

/-- The `arm8_ast` lowering of `AddCarry`: the zero compare, the conditional
compare, the first add-with-carry, the zeroing move and the second
add-with-carry. -/
theorem arm8Ast_addCarry (d rc sl sr : Nat) :
    arm8Ast (.inst (.arith (.addCarry d rc sl sr))) =
      [.Data (.«AddSubImmediate@64» (1, true, true, 0, sr, 31)),
       .Data (.«ConditionalCompareImmediate@64»
         (1, false, 0, 0, (false, false, true, false), rc)),
       .Data (.«AddSubCarry@64» (1, false, true, sl, rc, d)),
       .Data (.«MoveWide@64» (1, .z, 0, 0, sr)),
       .Data (.«AddSubCarry@64» (1, false, false, 31, sr, sr))] := rfl

/-- The encoded bytes of the `addCarry` lowering, as a concatenation. -/
theorem arm8Enc_addCarry (d rc sl sr : Nat) :
    arm8Enc (.inst (.arith (.addCarry d rc sl sr))) =
      arm8Encode (.Data (.«AddSubImmediate@64»
        (1, true, true, 0, BitVec.ofNat 5 sr, 31))) ++
      arm8Encode (.Data (.«ConditionalCompareImmediate@64»
        (1, false, 0, 0, (false, false, true, false), BitVec.ofNat 5 rc))) ++
      arm8Encode (.Data (.«AddSubCarry@64»
        (1, false, true, BitVec.ofNat 5 sl, BitVec.ofNat 5 rc, BitVec.ofNat 5 d))) ++
      arm8Encode (.Data (.«MoveWide@64»
        (1, .z, 0, 0, BitVec.ofNat 5 sr))) ++
      arm8Encode (.Data (.«AddSubCarry@64»
        (1, false, false, 31, BitVec.ofNat 5 sr, BitVec.ofNat 5 sr))) := by
  rw [arm8Enc, arm8Ast_addCarry]
  simp

/-- The `addCarry` lowering encodes to twenty bytes. -/
theorem arm8Enc_addCarry_length (d rc sl sr : Nat) :
    (arm8Enc (.inst (.arith (.addCarry d rc sl sr)))).length = 20 := by
  rw [arm8Enc_addCarry]
  simp [arm8Encode_length]

/-- The register-validity conjuncts of an `addCarry` `asm_ok`. -/
theorem arm8RegOk_addCarry (d rc sl sr : Nat)
    (h : asmOkExact (.inst (.arith (.addCarry d rc sl sr))) arm8ConfigL3 = true) :
    asmRegOkExact d arm8ConfigL3 = true ∧ asmRegOkExact rc arm8ConfigL3 = true ∧
      asmRegOkExact sl arm8ConfigL3 = true ∧ asmRegOkExact sr arm8ConfigL3 = true := by
  simp only [asmOkExact, arm8ConfigL3, asmInstOkExact, asmArithOkExact, Bool.and_eq_true,
    Bool.not_false, Bool.true_or, Bool.true_and] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩



/-! ## Assembling the `addCarry` case -/

/-- `holAligned 2` after five more four-byte words. -/
theorem holAligned_add_twenty (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 20) = true := by
  have h20 : holAligned 2 (20 : BitVec 64) = true := by rw [holAligned_iff]; decide
  rw [(alignedAddSub 2 pc 20 h20).1, h]

/-- The five aligned four-byte windows of a 20-byte code block. -/
theorem mem_allPcs_twenty_l3 (p : BitVec 64) (i : Nat) (hi : i < 5) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs 20 p 2 := by
  rw [allPcs_eq]
  refine ⟨i, ?_, rfl⟩
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  omega

/-- Byte offsets inside the fourth instruction word. -/
theorem bvAddCarry16_1 (a : BitVec 64) : a + 16 + 1 = a + 17 := by
  rw [BitVec.add_assoc]; congr 1
theorem bvAddCarry16_2 (a : BitVec 64) : a + 16 + 2 = a + 18 := by
  rw [BitVec.add_assoc]; congr 1
theorem bvAddCarry16_3 (a : BitVec 64) : a + 16 + 3 = a + 19 := by
  rw [BitVec.add_assoc]; congr 1

/-- The `EQ` condition code reads the `Z` flag. -/
theorem conditionHolds_eq (s : arm8_state) :
    ConditionHolds (0 : BitVec 4) s = s.PSTATE.Z := by
  unfold ConditionHolds
  simp only [ConditionTest, Flapjack.RiscV.L3.holWordExtract]
  rfl

/-- Reading a register other than the zero register. -/
theorem arm8X_reg (s : arm8_state) (n : BitVec 5) (hn : n ≠ (31 : BitVec 5)) :
    X (TN := 64) n s = s.REG n := by
  have hbeq : (n == BitVec.ofNat 5 31) = false := beq_eq_false_iff_ne.mpr hn
  simp only [X, hbeq, Bool.false_eq_true, if_false, BitVec.setWidth_eq]

/-- The value half of the rendered `AddWithCarry`. -/
theorem arm8AddWithCarry_value (x y : BitVec 64) (c : Bool) :
    (AddWithCarry (TN := 64) (x, (y, c))).1 =
      BitVec.ofNat 64 (x.toNat + y.toNat + (if c then 1 else 0)) := by
  rw [arm8AddWithCarry_machine]
  rfl

/-- The carry flag of the rendered `AddWithCarry` is the unsigned overflow. -/
theorem arm8AddWithCarry_carry (x y : BitVec 64) (c : Bool) :
    (AddWithCarry (TN := 64) (x, (y, c))).2.2.2.1 =
      decide (2 ^ 64 ≤ x.toNat + y.toNat + (if c then 1 else 0)) := by
  rw [arm8AddWithCarry_machine]
  show decide ((addWithCarry x y c).1.toNat ≠
    x.toNat + y.toNat + (if c then 1 else 0)) = _
  rw [show (addWithCarry x y c).1.toNat =
    (x.toNat + y.toNat + (if c then 1 else 0)) % 2 ^ 64 from rfl, decide_eq_decide]
  by_cases h : x.toNat + y.toNat + (if c then 1 else 0) < 2 ^ 64
  · rw [Nat.mod_eq_of_lt h]
    exact ⟨fun hh => absurd rfl hh, fun hle => absurd hle (Nat.not_le.mpr h)⟩
  · have hge : 2 ^ 64 ≤ x.toNat + y.toNat + (if c then 1 else 0) := Nat.le_of_not_lt h
    have hne : (x.toNat + y.toNat + (if c then 1 else 0)) % 2 ^ 64 ≠
        x.toNat + y.toNat + (if c then 1 else 0) := by
      intro hh
      have := Nat.mod_lt (x.toNat + y.toNat + (if c then 1 else 0)) (by norm_num : 0 < 2 ^ 64)
      omega
    exact ⟨fun _ => hge, fun _ => hne⟩

/-! ## The five intermediate states -/

/-- The state after `SUBS XZR, sr, #0`. -/
abbrev arm8AddCarryT1 (ms : arm8_state) (sr : BitVec 5) : arm8_state :=
  { ms with
    branch_hint := none,
    PC := ms.PC + 4,
    PSTATE :=
      { ms.PSTATE with
        N := BitVec.msb (X (TN := 64) sr ms),
        Z := (X (TN := 64) sr ms) == (0 : BitVec 64),
        C := true,
        V := false } }

/-- The state after `CCMP rc, #0, #0, EQ`. -/
noncomputable abbrev arm8AddCarryT2 (ms : arm8_state) (rc sr : BitVec 5) : arm8_state :=
  if ConditionHolds (0 : BitVec 4) (arm8AddCarryT1 ms sr) then
    { arm8AddCarryT1 ms sr with
      branch_hint := none,
      PC := (arm8AddCarryT1 ms sr).PC + 4,
      PSTATE :=
        { (arm8AddCarryT1 ms sr).PSTATE with
          N := BitVec.msb (X (TN := 64) rc (arm8AddCarryT1 ms sr)),
          Z := (X (TN := 64) rc (arm8AddCarryT1 ms sr)) == (0 : BitVec 64),
          C := false,
          V := false } }
  else
    { arm8AddCarryT1 ms sr with
      branch_hint := none,
      PC := (arm8AddCarryT1 ms sr).PC + 4,
      PSTATE :=
        { (arm8AddCarryT1 ms sr).PSTATE with
          N := false,
          Z := false,
          C := true,
          V := false } }

/-- The state after `ADC d, rc, sl`. -/
noncomputable abbrev arm8AddCarryT3 (ms : arm8_state) (d rc sl sr : BitVec 5) : arm8_state :=
  { arm8AddCarryT2 ms rc sr with
    branch_hint := none,
    PC := (arm8AddCarryT2 ms rc sr).PC + 4,
    REG :=
      holUpdate d
        (AddWithCarry (TN := 64)
          (X (TN := 64) rc (arm8AddCarryT2 ms rc sr),
            (X (TN := 64) sl (arm8AddCarryT2 ms rc sr),
              (arm8AddCarryT2 ms rc sr).PSTATE.C))).1
        (arm8AddCarryT2 ms rc sr).REG,
    PSTATE :=
      (SetTheFlags (true,
        (AddWithCarry (TN := 64)
          (X (TN := 64) rc (arm8AddCarryT2 ms rc sr),
            (X (TN := 64) sl (arm8AddCarryT2 ms rc sr),
              (arm8AddCarryT2 ms rc sr).PSTATE.C))).2)
        (arm8AddCarryT2 ms rc sr)).PSTATE }

/-- The state after `MOVZ sr, #0`. -/
noncomputable abbrev arm8AddCarryT4 (ms : arm8_state) (d rc sl sr : BitVec 5) : arm8_state :=
  { arm8AddCarryT3 ms d rc sl sr with
    branch_hint := none,
    PC := (arm8AddCarryT3 ms d rc sl sr).PC + 4,
    REG := holUpdate sr (0 : BitVec 64) (arm8AddCarryT3 ms d rc sl sr).REG }

/-- The state after the closing `ADC sr, sr, XZR`. -/
noncomputable abbrev arm8AddCarryT5 (ms : arm8_state) (d rc sl sr : BitVec 5) : arm8_state :=
  { arm8AddCarryT4 ms d rc sl sr with
    branch_hint := none,
    PC := (arm8AddCarryT4 ms d rc sl sr).PC + 4,
    REG :=
      holUpdate sr
        (AddWithCarry (TN := 64)
          (X (TN := 64) sr (arm8AddCarryT4 ms d rc sl sr),
            (X (TN := 64) (31 : BitVec 5) (arm8AddCarryT4 ms d rc sl sr),
              (arm8AddCarryT4 ms d rc sl sr).PSTATE.C))).1
        (arm8AddCarryT4 ms d rc sl sr).REG,
    PSTATE :=
      (SetTheFlags (false,
        (AddWithCarry (TN := 64)
          (X (TN := 64) sr (arm8AddCarryT4 ms d rc sl sr),
            (X (TN := 64) (31 : BitVec 5) (arm8AddCarryT4 ms d rc sl sr),
              (arm8AddCarryT4 ms d rc sl sr).PSTATE.C))).2)
        (arm8AddCarryT4 ms d rc sl sr)).PSTATE }

/-! ## Structural facts about the intermediate states -/

theorem arm8AddCarryT1_pc (ms : arm8_state) (sr : BitVec 5) :
    (arm8AddCarryT1 ms sr).PC = ms.PC + 4 := rfl

theorem arm8AddCarryT2_pc (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).PC = ms.PC + 8 := by
  dsimp only [arm8AddCarryT2]
  split <;> bv_omega

theorem arm8AddCarryT3_pc (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT3 ms d rc sl sr).PC = ms.PC + 12 := by
  show (arm8AddCarryT2 ms rc sr).PC + 4 = ms.PC + 12
  rw [arm8AddCarryT2_pc ms rc sr, BitVec.add_assoc]
  congr 1

theorem arm8AddCarryT4_pc (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT4 ms d rc sl sr).PC = ms.PC + 16 := by
  show (arm8AddCarryT3 ms d rc sl sr).PC + 4 = ms.PC + 16
  rw [arm8AddCarryT3_pc ms d rc sl sr, BitVec.add_assoc]
  congr 1

theorem arm8AddCarryT5_pc (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT5 ms d rc sl sr).PC = ms.PC + 20 := by
  show (arm8AddCarryT4 ms d rc sl sr).PC + 4 = ms.PC + 20
  rw [arm8AddCarryT4_pc ms d rc sl sr, BitVec.add_assoc]
  congr 1

theorem arm8AddCarryT1_reg (ms : arm8_state) (sr : BitVec 5) :
    (arm8AddCarryT1 ms sr).REG = ms.REG := rfl

theorem arm8AddCarryT2_reg (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).REG = ms.REG := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT1_exc (ms : arm8_state) (sr : BitVec 5) :
    (arm8AddCarryT1 ms sr).exception = ms.exception := rfl

theorem arm8AddCarryT2_exc (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).exception = ms.exception := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT2_sctlr (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).SCTLR_EL1 = ms.SCTLR_EL1 := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT2_tcr (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).TCR_EL1 = ms.TCR_EL1 := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT1_el (ms : arm8_state) (sr : BitVec 5) :
    (arm8AddCarryT1 ms sr).PSTATE.EL = ms.PSTATE.EL := rfl

theorem arm8AddCarryT2_el (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).PSTATE.EL = ms.PSTATE.EL := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT3_el (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT3 ms d rc sl sr).PSTATE.EL = ms.PSTATE.EL := by
  have h := arm8AddCarryT2_el ms rc sr
  simp only [setTheFlags_eq]
  split_ifs <;> exact h

theorem arm8AddCarryT4_el (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT4 ms d rc sl sr).PSTATE.EL = ms.PSTATE.EL :=
  arm8AddCarryT3_el ms d rc sl sr

theorem arm8AddCarryT5_el (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT5 ms d rc sl sr).PSTATE.EL = ms.PSTATE.EL := by
  have h := arm8AddCarryT4_el ms d rc sl sr
  simp only [setTheFlags_eq]
  split_ifs <;> exact h

theorem arm8AddCarryT1_mem (ms : arm8_state) (sr : BitVec 5) :
    ∀ a, (arm8AddCarryT1 ms sr).MEM a = ms.MEM a := fun _ => rfl

theorem arm8AddCarryT2_mem (ms : arm8_state) (rc sr : BitVec 5) :
    ∀ a, (arm8AddCarryT2 ms rc sr).MEM a = ms.MEM a := by
  dsimp only [arm8AddCarryT2]
  split <;> intro a <;> rfl

theorem arm8AddCarryT3_mem (ms : arm8_state) (d rc sl sr : BitVec 5) :
    ∀ a, (arm8AddCarryT3 ms d rc sl sr).MEM a = ms.MEM a :=
  fun a => arm8AddCarryT2_mem ms rc sr a

theorem arm8AddCarryT4_mem (ms : arm8_state) (d rc sl sr : BitVec 5) :
    ∀ a, (arm8AddCarryT4 ms d rc sl sr).MEM a = ms.MEM a :=
  fun a => arm8AddCarryT3_mem ms d rc sl sr a

theorem arm8AddCarryT5_mem (ms : arm8_state) (d rc sl sr : BitVec 5) :
    ∀ a, (arm8AddCarryT5 ms d rc sl sr).MEM a = ms.MEM a :=
  fun a => arm8AddCarryT4_mem ms d rc sl sr a

/-! ## `arm8_ok` at each intermediate state -/

theorem arm8Ok_of (ms s : arm8_state)
    (hel : s.PSTATE.EL = ms.PSTATE.EL)
    (hsctlr : s.SCTLR_EL1 = ms.SCTLR_EL1)
    (htcr : s.TCR_EL1 = ms.TCR_EL1)
    (hexc : s.exception = ms.exception)
    (hpc : holAligned 2 s.PC = true)
    (hok : arm8Ok ms = true) : arm8Ok s = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := (arm8Ok_iff ms).mp hok
  rw [arm8Ok_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hpc⟩
  · rw [hel]; exact h1
  · rw [hsctlr]; exact h2
  · rw [hsctlr]; exact h3
  · rw [htcr]; exact h4
  · rw [htcr]; exact h5
  · rw [hexc]; exact h6

theorem arm8Ok_addCarryT1 (ms : arm8_state) (sr : BitVec 5)
    (hal : holAligned 2 (ms.PC + 4) = true) (hok : arm8Ok ms = true) :
    arm8Ok (arm8AddCarryT1 ms sr) = true :=
  arm8Ok_of ms _ rfl rfl rfl rfl hal hok

theorem arm8Ok_addCarryT2 (ms : arm8_state) (rc sr : BitVec 5)
    (hal : holAligned 2 (ms.PC + 8) = true) (hok : arm8Ok ms = true) :
    arm8Ok (arm8AddCarryT2 ms rc sr) = true :=
  arm8Ok_of ms _ (arm8AddCarryT2_el ms rc sr) (arm8AddCarryT2_sctlr ms rc sr)
    (arm8AddCarryT2_tcr ms rc sr) (arm8AddCarryT2_exc ms rc sr)
    (by rw [arm8AddCarryT2_pc ms rc sr]; exact hal) hok

theorem arm8Ok_addCarryT3 (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hal : holAligned 2 (ms.PC + 12) = true) (hok : arm8Ok ms = true) :
    arm8Ok (arm8AddCarryT3 ms d rc sl sr) = true :=
  arm8Ok_of ms _ (arm8AddCarryT3_el ms d rc sl sr) (arm8AddCarryT2_sctlr ms rc sr)
    (arm8AddCarryT2_tcr ms rc sr) (arm8AddCarryT2_exc ms rc sr)
    (by rw [arm8AddCarryT3_pc ms d rc sl sr]; exact hal) hok

theorem arm8Ok_addCarryT4 (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hal : holAligned 2 (ms.PC + 16) = true) (hok : arm8Ok ms = true) :
    arm8Ok (arm8AddCarryT4 ms d rc sl sr) = true :=
  arm8Ok_of ms _ (arm8AddCarryT4_el ms d rc sl sr) (arm8AddCarryT2_sctlr ms rc sr)
    (arm8AddCarryT2_tcr ms rc sr) (arm8AddCarryT2_exc ms rc sr)
    (by rw [arm8AddCarryT4_pc ms d rc sl sr]; exact hal) hok

theorem arm8Ok_addCarryT5 (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hal : holAligned 2 (ms.PC + 20) = true) (hok : arm8Ok ms = true) :
    arm8Ok (arm8AddCarryT5 ms d rc sl sr) = true :=
  arm8Ok_of ms _ (arm8AddCarryT5_el ms d rc sl sr) (arm8AddCarryT2_sctlr ms rc sr)
    (arm8AddCarryT2_tcr ms rc sr) (arm8AddCarryT2_exc ms rc sr)
    (by rw [arm8AddCarryT5_pc ms d rc sl sr]; exact hal) hok

/-! ## The five `arm8Next` steps -/

theorem arm8Next_addCarryT1 (ms : arm8_state) (sr : BitVec 5)
    (hsr : sr ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms = arm8AddCarryT1 ms sr :=
  arm8Next_addSubImmediateS_zero ms sr hsr hexc0 h0 h1 h2 h3 hal he0 hel

theorem arm8Next_addCarryT2 (ms : arm8_state) (rc sr : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT1 ms sr).MEM (arm8AddCarryT1 ms sr).PC = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 0).toNat))
    (h1 : (arm8AddCarryT1 ms sr).MEM ((arm8AddCarryT1 ms sr).PC + 1) = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 8).toNat))
    (h2 : (arm8AddCarryT1 ms sr).MEM ((arm8AddCarryT1 ms sr).PC + 2) = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 16).toNat))
    (h3 : (arm8AddCarryT1 ms sr).MEM ((arm8AddCarryT1 ms sr).PC + 3) = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT1 ms sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next (arm8AddCarryT1 ms sr) = arm8AddCarryT2 ms rc sr :=
  arm8Next_conditionalCompare_zero (arm8AddCarryT1 ms sr) rc hexc0 h0 h1 h2 h3 hal he0 hel

theorem arm8Next_addCarryT3 (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hd : d ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT2 ms rc sr).MEM (arm8AddCarryT2 ms rc sr).PC = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 0).toNat))
    (h1 : (arm8AddCarryT2 ms rc sr).MEM ((arm8AddCarryT2 ms rc sr).PC + 1) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 8).toNat))
    (h2 : (arm8AddCarryT2 ms rc sr).MEM ((arm8AddCarryT2 ms rc sr).PC + 2) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 16).toNat))
    (h3 : (arm8AddCarryT2 ms rc sr).MEM ((arm8AddCarryT2 ms rc sr).PC + 3) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT2 ms rc sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next (arm8AddCarryT2 ms rc sr) = arm8AddCarryT3 ms d rc sl sr := by
  have hx : (arm8AddCarryT2 ms rc sr).exception = exception.NoException := by
    rw [arm8AddCarryT2_exc ms rc sr]; exact hexc0
  have hE : (arm8AddCarryT2 ms rc sr).SCTLR_EL1.E0E = false := by
    rw [arm8AddCarryT2_sctlr ms rc sr]; exact he0
  have hL : (arm8AddCarryT2 ms rc sr).PSTATE.EL = (0 : BitVec 2) := by
    rw [arm8AddCarryT2_el ms rc sr]; exact hel
  rw [arm8Next_addSubCarry (arm8AddCarryT2 ms rc sr) true sl rc d hd hx h0 h1 h2 h3 hal hE hL]

theorem arm8Next_addCarryT4 (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hsr : sr ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT3 ms d rc sl sr).MEM (arm8AddCarryT3 ms d rc sl sr).PC = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 0).toNat))
    (h1 : (arm8AddCarryT3 ms d rc sl sr).MEM ((arm8AddCarryT3 ms d rc sl sr).PC + 1) = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 8).toNat))
    (h2 : (arm8AddCarryT3 ms d rc sl sr).MEM ((arm8AddCarryT3 ms d rc sl sr).PC + 2) = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 16).toNat))
    (h3 : (arm8AddCarryT3 ms d rc sl sr).MEM ((arm8AddCarryT3 ms d rc sl sr).PC + 3) = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT3 ms d rc sl sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next (arm8AddCarryT3 ms d rc sl sr) = arm8AddCarryT4 ms d rc sl sr := by
  have hx : (arm8AddCarryT3 ms d rc sl sr).exception = exception.NoException := by
    show (arm8AddCarryT2 ms rc sr).exception = exception.NoException
    rw [arm8AddCarryT2_exc ms rc sr]; exact hexc0
  have hE : (arm8AddCarryT3 ms d rc sl sr).SCTLR_EL1.E0E = false := by
    show (arm8AddCarryT2 ms rc sr).SCTLR_EL1.E0E = false
    rw [arm8AddCarryT2_sctlr ms rc sr]; exact he0
  have hL : (arm8AddCarryT3 ms d rc sl sr).PSTATE.EL = (0 : BitVec 2) := by
    rw [arm8AddCarryT3_el ms d rc sl sr]; exact hel
  rw [arm8Next_moveWide_z_zero (arm8AddCarryT3 ms d rc sl sr) sr hsr hx h0 h1 h2 h3 hal hE hL]

theorem arm8Next_addCarryT5 (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hsr : sr ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT4 ms d rc sl sr).MEM (arm8AddCarryT4 ms d rc sl sr).PC = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 0).toNat))
    (h1 : (arm8AddCarryT4 ms d rc sl sr).MEM ((arm8AddCarryT4 ms d rc sl sr).PC + 1) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 8).toNat))
    (h2 : (arm8AddCarryT4 ms d rc sl sr).MEM ((arm8AddCarryT4 ms d rc sl sr).PC + 2) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 16).toNat))
    (h3 : (arm8AddCarryT4 ms d rc sl sr).MEM ((arm8AddCarryT4 ms d rc sl sr).PC + 3) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT4 ms d rc sl sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next (arm8AddCarryT4 ms d rc sl sr) = arm8AddCarryT5 ms d rc sl sr := by
  have hx : (arm8AddCarryT4 ms d rc sl sr).exception = exception.NoException := by
    show (arm8AddCarryT3 ms d rc sl sr).exception = exception.NoException
    show (arm8AddCarryT2 ms rc sr).exception = exception.NoException
    rw [arm8AddCarryT2_exc ms rc sr]; exact hexc0
  have hE : (arm8AddCarryT4 ms d rc sl sr).SCTLR_EL1.E0E = false := by
    show (arm8AddCarryT2 ms rc sr).SCTLR_EL1.E0E = false
    rw [arm8AddCarryT2_sctlr ms rc sr]; exact he0
  have hL : (arm8AddCarryT4 ms d rc sl sr).PSTATE.EL = (0 : BitVec 2) := by
    rw [arm8AddCarryT4_el ms d rc sl sr]; exact hel
  rw [arm8Next_addSubCarry (arm8AddCarryT4 ms d rc sl sr) false (31 : BitVec 5) sr sr
    hsr hx h0 h1 h2 h3 hal hE hL]

/-! ## The steps leave memory alone -/

theorem arm8Next_addCarryT1_mem (ms : arm8_state) (sr : BitVec 5)
    (hsr : sr ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false
      (holWordExtract 12 11 0 (0 : BitVec 64)) sr 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next ms).MEM x = ms.MEM x := by
  rw [arm8Next_addCarryT1 ms sr hsr hexc0 h0 h1 h2 h3 hal he0 hel]
  exact arm8AddCarryT1_mem ms sr

theorem arm8Next_addCarryT2_mem (ms : arm8_state) (rc sr : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT1 ms sr).MEM (arm8AddCarryT1 ms sr).PC = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 0).toNat))
    (h1 : (arm8AddCarryT1 ms sr).MEM ((arm8AddCarryT1 ms sr).PC + 1) = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 8).toNat))
    (h2 : (arm8AddCarryT1 ms sr).MEM ((arm8AddCarryT1 ms sr).PC + 2) = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 16).toNat))
    (h3 : (arm8AddCarryT1 ms sr).MEM ((arm8AddCarryT1 ms sr).PC + 3) = BitVec.ofNat 8
      ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4)
        false false true false rc >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT1 ms sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next (arm8AddCarryT1 ms sr)).MEM x = (arm8AddCarryT1 ms sr).MEM x := by
  rw [arm8Next_addCarryT2 ms rc sr hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  exact (arm8AddCarryT2_mem ms rc sr x).trans (arm8AddCarryT1_mem ms sr x).symm

theorem arm8Next_addCarryT3_mem (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hd : d ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT2 ms rc sr).MEM (arm8AddCarryT2 ms rc sr).PC = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 0).toNat))
    (h1 : (arm8AddCarryT2 ms rc sr).MEM ((arm8AddCarryT2 ms rc sr).PC + 1) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 8).toNat))
    (h2 : (arm8AddCarryT2 ms rc sr).MEM ((arm8AddCarryT2 ms rc sr).PC + 2) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 16).toNat))
    (h3 : (arm8AddCarryT2 ms rc sr).MEM ((arm8AddCarryT2 ms rc sr).PC + 3) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false true sl rc d >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT2 ms rc sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next (arm8AddCarryT2 ms rc sr)).MEM x = (arm8AddCarryT2 ms rc sr).MEM x := by
  rw [arm8Next_addCarryT3 ms d rc sl sr hd hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  exact (arm8AddCarryT3_mem ms d rc sl sr x).trans (arm8AddCarryT2_mem ms rc sr x).symm

theorem arm8Next_addCarryT4_mem (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hsr : sr ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT3 ms d rc sl sr).MEM (arm8AddCarryT3 ms d rc sl sr).PC = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 0).toNat))
    (h1 : (arm8AddCarryT3 ms d rc sl sr).MEM ((arm8AddCarryT3 ms d rc sl sr).PC + 1) = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 8).toNat))
    (h2 : (arm8AddCarryT3 ms d rc sl sr).MEM ((arm8AddCarryT3 ms d rc sl sr).PC + 2) = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 16).toNat))
    (h3 : (arm8AddCarryT3 ms d rc sl sr).MEM ((arm8AddCarryT3 ms d rc sl sr).PC + 3) = BitVec.ofNat 8
      ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) sr >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT3 ms d rc sl sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next (arm8AddCarryT3 ms d rc sl sr)).MEM x = (arm8AddCarryT3 ms d rc sl sr).MEM x := by
  rw [arm8Next_addCarryT4 ms d rc sl sr hsr hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  exact (arm8AddCarryT4_mem ms d rc sl sr x).trans (arm8AddCarryT3_mem ms d rc sl sr x).symm

theorem arm8Next_addCarryT5_mem (ms : arm8_state) (d rc sl sr : BitVec 5)
    (hsr : sr ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (h0 : (arm8AddCarryT4 ms d rc sl sr).MEM (arm8AddCarryT4 ms d rc sl sr).PC = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 0).toNat))
    (h1 : (arm8AddCarryT4 ms d rc sl sr).MEM ((arm8AddCarryT4 ms d rc sl sr).PC + 1) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 8).toNat))
    (h2 : (arm8AddCarryT4 ms d rc sl sr).MEM ((arm8AddCarryT4 ms d rc sl sr).PC + 2) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 16).toNat))
    (h3 : (arm8AddCarryT4 ms d rc sl sr).MEM ((arm8AddCarryT4 ms d rc sl sr).PC + 3) = BitVec.ofNat 8
      ((arm8AddSubCarryWord false false (31 : BitVec 5) sr sr >>> 24).toNat))
    (hal : Aligned (TN := 64) ((arm8AddCarryT4 ms d rc sl sr).PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next (arm8AddCarryT4 ms d rc sl sr)).MEM x = (arm8AddCarryT4 ms d rc sl sr).MEM x := by
  rw [arm8Next_addCarryT5 ms d rc sl sr hsr hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  exact (arm8AddCarryT5_mem ms d rc sl sr x).trans (arm8AddCarryT4_mem ms d rc sl sr x).symm


end Flapjack.Compiler.Encoders.Arm8.L3
