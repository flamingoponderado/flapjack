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

end Flapjack.Compiler.Encoders.Arm8.L3
