import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Compare
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.JumpCmp
import Flapjack.Compiler.Encoders.Arm8.ArithLemmas
import Flapjack.HolRef

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
  refine arm8Next_eq ms _ _ _ hdec ?_ rfl hexc0 h0 h1 h2 h3 hal he0 hel
  dsimp only [i]
  rw [hrun, if_neg hrd]
  rfl

/-! ## Projections through `SetTheFlags` and `write'X` -/

theorem arm8X_branchHint (n : BitVec 5) (s : arm8_state) :
    X (TN := 64) n { s with branch_hint := none } = X (TN := 64) n s := rfl

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
  refine arm8Next_eq ms _ _ _ hdec ?_ (by split <;> rfl) (by split <;> exact hexc0)
    h0 h1 h2 h3 hal he0 hel
  dsimp only [i]
  rw [hrun]
  simp only [setTheFlags_eq]
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
  refine arm8Next_eq ms _ _ _ hdec ?_ rfl hexc0 h0 h1 h2 h3 hal he0 hel
  dsimp only [i]
  rw [hrun]
  simp only [setTheFlags_eq]
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
  refine arm8L3Agree_next h hok _ _ (fun u => arm8Next_addSubImmediateS_zero u rn hrn) ?_ hf hb0 hb1 hb2 hb3
  have hx : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
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
  refine arm8L3Agree_next h hok _ _ (fun u => arm8Next_conditionalCompare_zero u rn) ?_ hf hb0 hb1 hb2 hb3
  have hx : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hcd : ConditionHolds (0 : BitVec 4) { s with branch_hint := none } =
      ConditionHolds (0 : BitVec 4) { t with branch_hint := none } :=
    arm8ConditionHolds_congr (0 : BitVec 4) (by rw [h.pstate])
  rw [hcd]
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
  refine arm8L3Agree_next h hok _ _ (fun u => arm8Next_addSubCarry u sb rm rn rd hrd) ?_ hf hb0 hb1 hb2 hb3
  have hx : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hxm : X (TN := 64) rm s = X (TN := 64) rm t := arm8X_congr_or_zero h rm
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
  refine arm8L3Agree_next h hok _ _ (fun u => arm8Next_moveWide_z_zero u rd hrd) ?_ hf hb0 hb1 hb2 hb3
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

theorem arm8AddCarryT2_reg (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).REG = ms.REG := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT2_exc (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).exception = ms.exception := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8ReadReg_eq (r : Nat) (s : AsmState 64) :
    Flapjack.Compiler.Encoders.AsmSem.readReg r s = s.regs r := rfl

theorem arm8AddCarryT3_exc (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT3 ms d rc sl sr).exception = ms.exception :=
  arm8AddCarryT2_exc ms rc sr

theorem arm8AddCarryT4_exc (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT4 ms d rc sl sr).exception = ms.exception :=
  arm8AddCarryT3_exc ms d rc sl sr

theorem arm8AddCarryT2_sctlr (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).SCTLR_EL1 = ms.SCTLR_EL1 := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT2_tcr (ms : arm8_state) (rc sr : BitVec 5) :
    (arm8AddCarryT2 ms rc sr).TCR_EL1 = ms.TCR_EL1 := by
  dsimp only [arm8AddCarryT2]
  split <;> rfl

theorem arm8AddCarryT3_sctlr (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT3 ms d rc sl sr).SCTLR_EL1 = ms.SCTLR_EL1 :=
  arm8AddCarryT2_sctlr ms rc sr

theorem arm8AddCarryT4_sctlr (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT4 ms d rc sl sr).SCTLR_EL1 = ms.SCTLR_EL1 :=
  arm8AddCarryT3_sctlr ms d rc sl sr

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

theorem arm8AddCarryT3_reg (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT3 ms d rc sl sr).REG =
      holUpdate d
        (AddWithCarry (TN := 64)
          (X (TN := 64) rc (arm8AddCarryT2 ms rc sr),
            (X (TN := 64) sl (arm8AddCarryT2 ms rc sr),
              (arm8AddCarryT2 ms rc sr).PSTATE.C))).1
        (arm8AddCarryT2 ms rc sr).REG := rfl

theorem arm8AddCarryT4_reg (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT4 ms d rc sl sr).REG =
      holUpdate sr (0 : BitVec 64) (arm8AddCarryT3 ms d rc sl sr).REG := rfl

theorem arm8AddCarryT5_reg (ms : arm8_state) (d rc sl sr : BitVec 5) :
    (arm8AddCarryT5 ms d rc sl sr).REG =
      holUpdate sr
        (AddWithCarry (TN := 64)
          (X (TN := 64) sr (arm8AddCarryT4 ms d rc sl sr),
            (X (TN := 64) (31 : BitVec 5) (arm8AddCarryT4 ms d rc sl sr),
              (arm8AddCarryT4 ms d rc sl sr).PSTATE.C))).1
        (arm8AddCarryT4 ms d rc sl sr).REG := rfl

/-- Adding two zeros and a carry-in. -/
theorem arm8AddWithCarry_xzr (c : Bool) :
    (AddWithCarry (TN := 64) ((0 : BitVec 64), ((0 : BitVec 64), c))).1 =
      if c then (1 : BitVec 64) else 0 := by
  rw [arm8AddWithCarry_value]
  by_cases h : c <;> simp [h]

/-- A `decide`d `if` is the plain `if`. -/
theorem iteDecide {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if decide p then a else b) = if p then a else b := by
  by_cases h : p <;> simp [h]

theorem arm8Next_conditionalCompare_zero_mem (s : arm8_state) (rc : BitVec 5)
    (hexc0 : s.exception = exception.NoException)
    (h0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5)
      (0 : BitVec 4) false false true false rc >>> 0).toNat))
    (h1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5)
      (0 : BitVec 4) false false true false rc >>> 8).toNat))
    (h2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5)
      (0 : BitVec 4) false false true false rc >>> 16).toNat))
    (h3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5)
      (0 : BitVec 4) false false true false rc >>> 24).toNat))
    (hal : Aligned (TN := 64) (s.PC, 4) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next s).MEM x = s.MEM x := by
  rw [arm8Next_conditionalCompare_zero s rc hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  split <;> rfl

theorem arm8Next_addSubCarry_mem (s : arm8_state) (sb : Bool) (rm rn rd : BitVec 5)
    (hrd : rd ≠ (31 : BitVec 5))
    (hexc0 : s.exception = exception.NoException)
    (h0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 0).toNat))
    (h1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 8).toNat))
    (h2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 16).toNat))
    (h3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8AddSubCarryWord false sb rm rn rd >>> 24).toNat))
    (hal : Aligned (TN := 64) (s.PC, 4) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next s).MEM x = s.MEM x := by
  rw [arm8Next_addSubCarry s sb rm rn rd hrd hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x; rfl

theorem arm8Next_moveWide_z_zero_mem (s : arm8_state) (rd : BitVec 5)
    (hrd : rd ≠ (31 : BitVec 5))
    (hexc0 : s.exception = exception.NoException)
    (h0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 0).toNat))
    (h1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 8).toNat))
    (h2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 16).toNat))
    (h3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) rd >>> 24).toNat))
    (hal : Aligned (TN := 64) (s.PC, 4) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next s).MEM x = s.MEM x := by
  rw [arm8Next_moveWide_z_zero s rd hrd hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x; rfl

/-- The `addCarry` constructor of `encoder_correct arm8TargetL3`: the five
instructions of the CakeML lowering (`SUBS XZR, sr, #0`; `CCMP rc, #0, #0, EQ`;
`ADC d, rc, sl`; `MOVZ sr, #0`; `ADC sr, sr, XZR`) compute the source-side
`arith_upd` sum and carry. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_addCarry (d rc sl sr : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.addCarry d rc sl sr))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.addCarry d rc sl sr))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change arm8Ok ms = true at hok
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
  have hregs := arm8RegOk_addCarry d rc sl sr hs.2.2.2.2.2.2
  obtain ⟨hd_lt, hd_av, hd31⟩ := regOk_of_asmL3 hregs.1
  obtain ⟨hrc_lt, hrc_av, hrc31⟩ := regOk_of_asmL3 hregs.2.1
  obtain ⟨hsl_lt, hsl_av, hsl31⟩ := regOk_of_asmL3 hregs.2.2.1
  obtain ⟨hsr_lt, hsr_av, hsr31⟩ := regOk_of_asmL3 hregs.2.2.2
  have hd5 : (↑d) ≠ (31 : BitVec 5) := by
    intro hh
    apply hd31
    have ht : (BitVec.ofNat 5 d).toNat = 31 := by
      have h := congrArg BitVec.toNat hh
      rw [show (31 : BitVec 5).toNat = 31 from by decide] at h
      exact h
    rw [BitVec.toNat_ofNat] at ht
    have hd32 : d % 2 ^ 5 = d := Nat.mod_eq_of_lt (by omega)
    omega
  have hrc5 : (↑rc) ≠ (31 : BitVec 5) := by
    intro hh
    apply hrc31
    have ht : (BitVec.ofNat 5 rc).toNat = 31 := by
      have h := congrArg BitVec.toNat hh
      rw [show (31 : BitVec 5).toNat = 31 from by decide] at h
      exact h
    rw [BitVec.toNat_ofNat] at ht
    have hrc32 : rc % 2 ^ 5 = rc := Nat.mod_eq_of_lt (by omega)
    omega
  have hsl5 : (↑sl) ≠ (31 : BitVec 5) := by
    intro hh
    apply hsl31
    have ht : (BitVec.ofNat 5 sl).toNat = 31 := by
      have h := congrArg BitVec.toNat hh
      rw [show (31 : BitVec 5).toNat = 31 from by decide] at h
      exact h
    rw [BitVec.toNat_ofNat] at ht
    have hsl32 : sl % 2 ^ 5 = sl := Nat.mod_eq_of_lt (by omega)
    omega
  have hsr5 : (↑sr) ≠ (31 : BitVec 5) := by
    intro hh
    apply hsr31
    have ht : (BitVec.ofNat 5 sr).toNat = 31 := by
      have h := congrArg BitVec.toNat hh
      rw [show (31 : BitVec 5).toNat = 31 from by decide] at h
      exact h
    rw [BitVec.toNat_ofNat] at ht
    have hsr32 : sr % 2 ^ 5 = sr := Nat.mod_eq_of_lt (by omega)
    omega
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := aligned_of_holAligned ms.PC halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.arith (.addCarry d rc sl sr))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have henclen := arm8Enc_addCarry_length d rc sl sr
  have hlow0 : (0 : BitVec 64) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by decide
  have henc := arm8Enc_addCarry d rc sl sr
  rw [arm8EncodeBytes_addSubImmediateS_low true 0 (BitVec.ofNat 5 sr) 31 hlow0,
    arm8EncodeBytes_conditionalCompare (BitVec.ofNat 5 rc),
    arm8EncodeBytes_addSubCarry true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d),
    arm8EncodeBytes_moveWide_z_zero (BitVec.ofNat 5 sr),
    arm8EncodeBytes_addSubCarry false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr)] at henc
  have hbyte (i : Nat) (hi : i < 20) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) =
        (arm8Enc (.inst (.arith (.addCarry d rc sl sr)))).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [henclen]; exact hi)

  have hb0 : ms.MEM (ms.PC + BitVec.ofNat 64 0) =
      BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false (holWordExtract 12 11 0 (0 : BitVec 64)) (BitVec.ofNat 5 sr) 31 >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb1 : ms.MEM (ms.PC + BitVec.ofNat 64 1) =
      BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false (holWordExtract 12 11 0 (0 : BitVec 64)) (BitVec.ofNat 5 sr) 31 >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb2 : ms.MEM (ms.PC + BitVec.ofNat 64 2) =
      BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false (holWordExtract 12 11 0 (0 : BitVec 64)) (BitVec.ofNat 5 sr) 31 >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb3 : ms.MEM (ms.PC + BitVec.ofNat 64 3) =
      BitVec.ofNat 8 ((arm8AddSubImmediateWordS true false (holWordExtract 12 11 0 (0 : BitVec 64)) (BitVec.ofNat 5 sr) 31 >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb4 : ms.MEM (ms.PC + BitVec.ofNat 64 4) =
      BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 0).toNat) := by
    have hh := hbyte 4 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb5 : ms.MEM (ms.PC + BitVec.ofNat 64 5) =
      BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 8).toNat) := by
    have hh := hbyte 5 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb6 : ms.MEM (ms.PC + BitVec.ofNat 64 6) =
      BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 16).toNat) := by
    have hh := hbyte 6 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb7 : ms.MEM (ms.PC + BitVec.ofNat 64 7) =
      BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 24).toNat) := by
    have hh := hbyte 7 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb8 : ms.MEM (ms.PC + BitVec.ofNat 64 8) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 0).toNat) := by
    have hh := hbyte 8 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb9 : ms.MEM (ms.PC + BitVec.ofNat 64 9) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 8).toNat) := by
    have hh := hbyte 9 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb10 : ms.MEM (ms.PC + BitVec.ofNat 64 10) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 16).toNat) := by
    have hh := hbyte 10 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb11 : ms.MEM (ms.PC + BitVec.ofNat 64 11) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 24).toNat) := by
    have hh := hbyte 11 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb12 : ms.MEM (ms.PC + BitVec.ofNat 64 12) =
      BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 0).toNat) := by
    have hh := hbyte 12 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb13 : ms.MEM (ms.PC + BitVec.ofNat 64 13) =
      BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 8).toNat) := by
    have hh := hbyte 13 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb14 : ms.MEM (ms.PC + BitVec.ofNat 64 14) =
      BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 16).toNat) := by
    have hh := hbyte 14 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb15 : ms.MEM (ms.PC + BitVec.ofNat 64 15) =
      BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 24).toNat) := by
    have hh := hbyte 15 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb16 : ms.MEM (ms.PC + BitVec.ofNat 64 16) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 0).toNat) := by
    have hh := hbyte 16 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb17 : ms.MEM (ms.PC + BitVec.ofNat 64 17) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 8).toNat) := by
    have hh := hbyte 17 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb18 : ms.MEM (ms.PC + BitVec.ofNat 64 18) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 16).toNat) := by
    have hh := hbyte 18 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb19 : ms.MEM (ms.PC + BitVec.ofNat 64 19) =
      BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 24).toNat) := by
    have hh := hbyte 19 (by norm_num)
    rw [henc] at hh
    simpa using hh

  have ht1b0 : ((arm8AddCarryT1 ms sr)).MEM ((arm8AddCarryT1 ms sr)).PC = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 0).toNat) := hb4
  have ht1b1 : ((arm8AddCarryT1 ms sr)).MEM (((arm8AddCarryT1 ms sr)).PC + 1) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 8).toNat) := by
    rw [show ((arm8AddCarryT1 ms sr)).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_1]
    exact hb5
  have ht1b2 : ((arm8AddCarryT1 ms sr)).MEM (((arm8AddCarryT1 ms sr)).PC + 2) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 16).toNat) := by
    rw [show ((arm8AddCarryT1 ms sr)).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_2]
    exact hb6
  have ht1b3 : ((arm8AddCarryT1 ms sr)).MEM (((arm8AddCarryT1 ms sr)).PC + 3) = BitVec.ofNat 8 ((arm8ConditionalCompareWord false (0 : BitVec 5) (0 : BitVec 4) false false true false (BitVec.ofNat 5 rc) >>> 24).toNat) := by
    rw [show ((arm8AddCarryT1 ms sr)).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_3]
    exact hb7

  have ht2b0 : ((arm8AddCarryT2 ms rc sr)).MEM ((arm8AddCarryT2 ms rc sr)).PC = BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 0).toNat) := by
    rw [arm8AddCarryT2_pc ms rc sr, arm8AddCarryT2_mem ms rc sr]
    exact hb8
  have ht2b1 : ((arm8AddCarryT2 ms rc sr)).MEM (((arm8AddCarryT2 ms rc sr)).PC + 1) = BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 8).toNat) := by
    rw [arm8AddCarryT2_pc ms rc sr, arm8AddCarryT2_mem ms rc sr, bv_add_8_1]
    exact hb9
  have ht2b2 : ((arm8AddCarryT2 ms rc sr)).MEM (((arm8AddCarryT2 ms rc sr)).PC + 2) = BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 16).toNat) := by
    rw [arm8AddCarryT2_pc ms rc sr, arm8AddCarryT2_mem ms rc sr, bv_add_8_2]
    exact hb10
  have ht2b3 : ((arm8AddCarryT2 ms rc sr)).MEM (((arm8AddCarryT2 ms rc sr)).PC + 3) = BitVec.ofNat 8 ((arm8AddSubCarryWord false true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) >>> 24).toNat) := by
    rw [arm8AddCarryT2_pc ms rc sr, arm8AddCarryT2_mem ms rc sr, bv_add_8_3]
    exact hb11

  have ht3b0 : ((arm8AddCarryT3 ms d rc sl sr)).MEM ((arm8AddCarryT3 ms d rc sl sr)).PC = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 0).toNat) := by
    rw [arm8AddCarryT3_pc ms d rc sl sr, arm8AddCarryT3_mem ms d rc sl sr]
    exact hb12
  have ht3b1 : ((arm8AddCarryT3 ms d rc sl sr)).MEM (((arm8AddCarryT3 ms d rc sl sr)).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 8).toNat) := by
    rw [arm8AddCarryT3_pc ms d rc sl sr, arm8AddCarryT3_mem ms d rc sl sr, bv_add_12_1]
    exact hb13
  have ht3b2 : ((arm8AddCarryT3 ms d rc sl sr)).MEM (((arm8AddCarryT3 ms d rc sl sr)).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 16).toNat) := by
    rw [arm8AddCarryT3_pc ms d rc sl sr, arm8AddCarryT3_mem ms d rc sl sr, bv_add_12_2]
    exact hb14
  have ht3b3 : ((arm8AddCarryT3 ms d rc sl sr)).MEM (((arm8AddCarryT3 ms d rc sl sr)).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .z (0 : BitVec 2) (0 : BitVec 16) (BitVec.ofNat 5 sr) >>> 24).toNat) := by
    rw [arm8AddCarryT3_pc ms d rc sl sr, arm8AddCarryT3_mem ms d rc sl sr, bv_add_12_3]
    exact hb15

  have ht4b0 : ((arm8AddCarryT4 ms d rc sl sr)).MEM ((arm8AddCarryT4 ms d rc sl sr)).PC = BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 0).toNat) := by
    rw [arm8AddCarryT4_pc ms d rc sl sr, arm8AddCarryT4_mem ms d rc sl sr]
    exact hb16
  have ht4b1 : ((arm8AddCarryT4 ms d rc sl sr)).MEM (((arm8AddCarryT4 ms d rc sl sr)).PC + 1) = BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 8).toNat) := by
    rw [arm8AddCarryT4_pc ms d rc sl sr, arm8AddCarryT4_mem ms d rc sl sr, bvAddCarry16_1]
    exact hb17
  have ht4b2 : ((arm8AddCarryT4 ms d rc sl sr)).MEM (((arm8AddCarryT4 ms d rc sl sr)).PC + 2) = BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 16).toNat) := by
    rw [arm8AddCarryT4_pc ms d rc sl sr, arm8AddCarryT4_mem ms d rc sl sr, bvAddCarry16_2]
    exact hb18
  have ht4b3 : ((arm8AddCarryT4 ms d rc sl sr)).MEM (((arm8AddCarryT4 ms d rc sl sr)).PC + 3) = BitVec.ofNat 8 ((arm8AddSubCarryWord false false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) >>> 24).toNat) := by
    rw [arm8AddCarryT4_pc ms d rc sl sr, arm8AddCarryT4_mem ms d rc sl sr, bvAddCarry16_3]
    exact hb19

  have hal4 : holAligned 2 (ms.PC + 4) = true := holAligned_add_four ms.PC halign
  have hal8 : holAligned 2 (ms.PC + 8) = true := holAligned_add_eight ms.PC halign
  have hal12 : holAligned 2 (ms.PC + 12) = true := holAligned_add_twelve ms.PC halign
  have hal16 : holAligned 2 (ms.PC + 16) = true := holAligned_add_sixteen ms.PC halign
  have hal20 : holAligned 2 (ms.PC + 20) = true := holAligned_add_twenty ms.PC halign
  have hal4a : Aligned (TN := 64) (ms.PC + 4, 4) = true := aligned_of_holAligned _ hal4
  have hal8a : Aligned (TN := 64) (ms.PC + 8, 4) = true := aligned_of_holAligned _ hal8
  have hal12a : Aligned (TN := 64) (ms.PC + 12, 4) = true := aligned_of_holAligned _ hal12
  have hal16a : Aligned (TN := 64) (ms.PC + 16, 4) = true := aligned_of_holAligned _ hal16
  have hal20a : Aligned (TN := 64) (ms.PC + 20, 4) = true := aligned_of_holAligned _ hal20
  have hXrc : X (TN := 64) (↑rc) (arm8AddCarryT2 ms rc sr) = s1.regs rc := by
    rw [arm8X_reg _ _ hrc5, arm8AddCarryT2_reg]
    exact hreg rc ⟨by simpa [arm8ConfigL3] using hrc_lt, hrc_av⟩
  have hXsl : X (TN := 64) (↑sl) (arm8AddCarryT2 ms rc sr) = s1.regs sl := by
    rw [arm8X_reg _ _ hsl5, arm8AddCarryT2_reg]
    exact hreg sl ⟨by simpa [arm8ConfigL3] using hsl_lt, hsl_av⟩
  have hXsr : X (TN := 64) (↑sr) ms = s1.regs sr := by
    rw [arm8X_reg _ _ hsr5]
    exact hreg sr ⟨by simpa [arm8ConfigL3] using hsr_lt, hsr_av⟩
  have hC2 : (arm8AddCarryT2 ms rc sr).PSTATE.C =
      (X (TN := 64) (↑sr) ms != (0 : BitVec 64)) := by
    have h1 : (arm8AddCarryT2 ms rc sr).PSTATE.C =
        if ConditionHolds (0 : BitVec 4) (arm8AddCarryT1 ms sr) then false else true := by
      dsimp only [arm8AddCarryT2]
      split <;> rfl
    have h2 : (arm8AddCarryT2 ms rc sr).PSTATE.C =
        !(arm8AddCarryT1 ms sr).PSTATE.Z := by
      rw [h1, conditionHolds_eq]
      cases (arm8AddCarryT1 ms sr).PSTATE.Z <;> rfl
    rw [h2]
    rfl
  have hC2' : (if (arm8AddCarryT2 ms rc sr).PSTATE.C then (1 : Nat) else 0) =
      (if s1.regs sr = 0 then 0 else 1) := by
    rw [hC2, hXsr]
    by_cases hs : s1.regs sr = 0
    · simp_all
    · simp_all
  have hsumEq : (AddWithCarry (TN := 64)
      (X (TN := 64) (↑rc) (arm8AddCarryT2 ms rc sr),
        (X (TN := 64) (↑sl) (arm8AddCarryT2 ms rc sr),
          (arm8AddCarryT2 ms rc sr).PSTATE.C))).1 = BitVec.ofNat 64 ((s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1)) := by
    rw [arm8AddWithCarry_value, hXrc, hXsl, hC2']
  have hXsrT4 : X (TN := 64) (↑sr) (arm8AddCarryT4 ms d rc sl sr)
      = (0 : BitVec 64) := by
    rw [arm8X_reg _ _ hsr5]
    simp [holUpdate, Flapjack.RiscV.L3.holUpdate]
  have hC4 : (arm8AddCarryT4 ms d rc sl sr).PSTATE.C = decide (2 ^ 64 ≤ (s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1)) := by
    have h1 : (arm8AddCarryT4 ms d rc sl sr).PSTATE.C =
        (arm8AddCarryT3 ms d rc sl sr).PSTATE.C := rfl
    rw [h1]
    have h3 : (arm8AddCarryT3 ms d rc sl sr).PSTATE.C =
        (AddWithCarry (TN := 64)
          (X (TN := 64) (↑rc) (arm8AddCarryT2 ms rc sr),
            (X (TN := 64) (↑sl) (arm8AddCarryT2 ms rc sr),
              (arm8AddCarryT2 ms rc sr).PSTATE.C))).2.2.2.1 := by
      simp only [setTheFlags_eq]
      split_ifs <;> rfl
    rw [h3, arm8AddWithCarry_carry, hXrc, hXsl, hC2']
  have hcarryEq : (AddWithCarry (TN := 64)
      (X (TN := 64) (↑sr) (arm8AddCarryT4 ms d rc sl sr),
        (X (TN := 64) (31 : BitVec 5) (arm8AddCarryT4 ms d rc sl sr),
          (arm8AddCarryT4 ms d rc sl sr).PSTATE.C))).1 =
        if 2 ^ 64 ≤ (s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1) then (1 : BitVec 64) else 0 := by
    rw [show X (TN := 64) (↑sr) (arm8AddCarryT4 ms d rc sl sr)
        = (0 : BitVec 64) from hXsrT4,
      show X (TN := 64) (31 : BitVec 5) (arm8AddCarryT4 ms d rc sl sr)
        = (0 : BitVec 64) from arm8X_zero_ofNat _,
      arm8AddWithCarry_xzr, hC4, iteDecide]
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [henclen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 20 := by
    rw [← hupd]
    simp [asmUpd, instUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, updPc, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, updPc, updReg]
  have hs2regsR : ∀ k, s2.regs k =
      if k = sr then (if 2 ^ 64 ≤ (Flapjack.Compiler.Encoders.AsmSem.readReg rc s1).toNat + (Flapjack.Compiler.Encoders.AsmSem.readReg sl s1).toNat + (if Flapjack.Compiler.Encoders.AsmSem.readReg sr s1 = 0 then 0 else 1) then (1 : BitVec 64) else 0)
      else if k = d then BitVec.ofNat 64 ((Flapjack.Compiler.Encoders.AsmSem.readReg rc s1).toNat + (Flapjack.Compiler.Encoders.AsmSem.readReg sl s1).toNat + (if Flapjack.Compiler.Encoders.AsmSem.readReg sr s1 = 0 then 0 else 1))
      else s1.regs k := by
    intro k
    rw [← hupd]
    simp only [asmUpd, instUpd, arithUpd, updPc, updReg]
  have hs2regs : ∀ k, s2.regs k =
      if k = sr then (if 2 ^ 64 ≤ (s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1) then (1 : BitVec 64) else 0)
      else if k = d then BitVec.ofNat 64 ((s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1))
      else s1.regs k := by
    intro k
    rw [hs2regsR k, arm8ReadReg_eq rc s1, arm8ReadReg_eq sl s1, arm8ReadReg_eq sr s1]
  have hnext1 : arm8Next ms = arm8AddCarryT1 ms sr :=
    arm8Next_addCarryT1 ms sr hsr5 hexc0 (by simpa using hb0) hb1 hb2 hb3 hal he0 hel
  have hnext2 : arm8Next (arm8AddCarryT1 ms sr) = arm8AddCarryT2 ms rc sr :=
    arm8Next_addCarryT2 ms rc sr hexc0 ht1b0 ht1b1 ht1b2 ht1b3 hal4a he0 hel
  have hnext3 : arm8Next (arm8AddCarryT2 ms rc sr) = arm8AddCarryT3 ms d rc sl sr :=
    arm8Next_addCarryT3 ms d rc sl sr hd5 hexc0 ht2b0 ht2b1 ht2b2 ht2b3
      (by rw [arm8AddCarryT2_pc ms rc sr]; exact hal8a) he0 hel
  have hnext4 : arm8Next (arm8AddCarryT3 ms d rc sl sr) = arm8AddCarryT4 ms d rc sl sr :=
    arm8Next_addCarryT4 ms d rc sl sr hsr5 hexc0 ht3b0 ht3b1 ht3b2 ht3b3
      (by rw [arm8AddCarryT3_pc ms d rc sl sr]; exact hal12a) he0 hel
  have hnext5 : arm8Next (arm8AddCarryT4 ms d rc sl sr) = arm8AddCarryT5 ms d rc sl sr :=
    arm8Next_addCarryT5 ms d rc sl sr hsr5 hexc0 ht4b0 ht4b1 ht4b2 ht4b3
      (by rw [arm8AddCarryT4_pc ms d rc sl sr]; exact hal16a) he0 hel
  have hok1 : arm8Ok (arm8AddCarryT1 ms sr) = true := arm8Ok_addCarryT1 ms sr hal4 hok
  have hok2 : arm8Ok (arm8AddCarryT2 ms rc sr) = true := arm8Ok_addCarryT2 ms rc sr hal8 hok
  have hok3 : arm8Ok (arm8AddCarryT3 ms d rc sl sr) = true := arm8Ok_addCarryT3 ms d rc sl sr hal12 hok
  have hok4 : arm8Ok (arm8AddCarryT4 ms d rc sl sr) = true := arm8Ok_addCarryT4 ms d rc sl sr hal16 hok
  have hdom1 : ∀ j, j < 4 → s1.memDomain ((arm8AddCarryT1 ms sr).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8AddCarryT1 ms sr).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (4 + j) := by
      rw [arm8AddCarryT1_pc ms sr, hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom (4 + j) (by omega)
  have hdom2 : ∀ j, j < 4 → s1.memDomain ((arm8AddCarryT2 ms rc sr).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8AddCarryT2 ms rc sr).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (8 + j) := by
      rw [arm8AddCarryT2_pc ms rc sr, hpc]
      exact bv_add_split s1.pc 8 j
    rw [h1]
    exact hdom (8 + j) (by omega)
  have hdom3 : ∀ j, j < 4 → s1.memDomain ((arm8AddCarryT3 ms d rc sl sr).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8AddCarryT3 ms d rc sl sr).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (12 + j) := by
      rw [arm8AddCarryT3_pc ms d rc sl sr, hpc]
      exact bv_add_split s1.pc 12 j
    rw [h1]
    exact hdom (12 + j) (by omega)
  have hdom4 : ∀ j, j < 4 → s1.memDomain ((arm8AddCarryT4 ms d rc sl sr).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8AddCarryT4 ms d rc sl sr).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (16 + j) := by
      rw [arm8AddCarryT4_pc ms d rc sl sr, hpc]
      exact bv_add_split s1.pc 16 j
    rw [h1]
    exact hdom (16 + j) (by omega)


  have hq : targetStateRel arm8TargetL3 s2 (arm8AddCarryT5 ms d rc sl sr) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact arm8Ok_addCarryT5 ms d rc sl sr hal20 hok
    · change (arm8AddCarryT5 ms d rc sl sr).PC = s2.pc
      rw [arm8AddCarryT5_pc ms d rc sl sr, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → (arm8AddCarryT5 ms d rc sl sr).MEM a = s2.mem a
      intro a ha
      rw [hs2mem]
      exact (arm8AddCarryT5_mem ms d rc sl sr a).trans (hmem a (hs2dom ▸ ha))
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        (arm8AddCarryT5 ms d rc sl sr).REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
      have hT5 : (arm8AddCarryT5 ms d rc sl sr).REG (BitVec.ofNat 5 k) =
          if (BitVec.ofNat 5 sr) = (BitVec.ofNat 5 k) then
            (if 2 ^ 64 ≤ (s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1) then (1 : BitVec 64) else 0)
          else if (BitVec.ofNat 5 d) = (BitVec.ofNat 5 k) then BitVec.ofNat 64 ((s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1))
          else ms.REG (BitVec.ofNat 5 k) := by
        rw [arm8AddCarryT5_reg ms d rc sl sr, hcarryEq,
          arm8AddCarryT4_reg ms d rc sl sr, arm8AddCarryT3_reg ms d rc sl sr, hsumEq,
          arm8AddCarryT2_reg ms rc sr]
        simp only [holUpdate, Flapjack.RiscV.L3.holUpdate]
        by_cases h1 : (BitVec.ofNat 5 sr) = (BitVec.ofNat 5 k)
        · simp [h1]
        · simp [h1]
      rw [hT5, hs2regs k]
      by_cases hks : k = sr
      · have h1 : (BitVec.ofNat 5 sr) = (BitVec.ofNat 5 k) := by rw [hks]
        rw [if_pos h1, if_pos hks]
      · have h1 : ¬ ((BitVec.ofNat 5 sr) = (BitVec.ofNat 5 k)) := by
          intro hh
          have hk' : sr = k := (arm8Reg_eq hsr_lt hk32).mp hh
          exact hks hk'.symm
        rw [if_neg h1, if_neg hks]
        by_cases hkd : k = d
        · have h2 : (BitVec.ofNat 5 d) = (BitVec.ofNat 5 k) := by rw [hkd]
          rw [if_pos h2, if_pos hkd]
        · have h2 : ¬ ((BitVec.ofNat 5 d) = (BitVec.ofNat 5 k)) := by
            intro hh
            have hk' : d = k := (arm8Reg_eq hd_lt hk32).mp hh
            exact hkd hk'.symm
          rw [if_neg h2, if_neg hkd]
          exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  have hdom0 : ∀ j, j < 4 → s1.memDomain (ms.PC + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hpc]
    exact hdom j (by rw [henclen]; omega)
  let T : Nat → arm8_state := fun k => match k with
    | 0 => ms
    | 1 => arm8AddCarryT1 ms sr
    | 2 => arm8AddCarryT2 ms rc sr
    | 3 => arm8AddCarryT3 ms d rc sl sr
    | 4 => arm8AddCarryT4 ms d rc sl sr
    | _ => arm8AddCarryT5 ms d rc sl sr
  have hchain : ∀ k u, ChainAt s1.memDomain ms T k u → Arm8L3Agree s1.memDomain u (T k) := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      rw [hu.1 rfl]
      exact Arm8L3Agree.refl _ _
    · exact hu.2 hk
  refine asmCaseChain _ 4 T s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ henclen
    ?_ ?_ ?_ ?_ ?_ hs2dom hq
  · intro k hk u hu'
    have hu := hchain k u hu'
    interval_cases k
    · have hh := arm8Next_addSubImmediateS_zero_agree s1.memDomain u ms hu
        (by rw [arm8Ok_congr hu]; exact hok) (BitVec.ofNat 5 sr) hsr5 hdom0
        (by simpa using hb0) hb1 hb2 hb3
      rw [hnext1] at hh
      exact hh
    · have hh := arm8Next_conditionalCompare_zero_agree s1.memDomain u
        (arm8AddCarryT1 ms sr) hu (by rw [arm8Ok_congr hu]; exact hok1)
        (BitVec.ofNat 5 rc) hdom1 ht1b0 ht1b1 ht1b2 ht1b3
      rw [hnext2] at hh
      exact hh
    · have hh := arm8Next_addSubCarry_agree s1.memDomain u
        (arm8AddCarryT2 ms rc sr) hu (by rw [arm8Ok_congr hu]; exact hok2)
        true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc) (BitVec.ofNat 5 d) hd5
        hdom2 ht2b0 ht2b1 ht2b2 ht2b3
      rw [hnext3] at hh
      exact hh
    · have hh := arm8Next_moveWide_z_zero_agree s1.memDomain u
        (arm8AddCarryT3 ms d rc sl sr) hu (by rw [arm8Ok_congr hu]; exact hok3)
        (BitVec.ofNat 5 sr) hsr5 hdom3 ht3b0 ht3b1 ht3b2 ht3b3
      rw [hnext4] at hh
      exact hh
    · have hh := arm8Next_addSubCarry_agree s1.memDomain u
        (arm8AddCarryT4 ms d rc sl sr) hu (by rw [arm8Ok_congr hu]; exact hok4)
        false (31 : BitVec 5) (BitVec.ofNat 5 sr) (BitVec.ofNat 5 sr) hsr5
        hdom4 ht4b0 ht4b1 ht4b2 ht4b3
      rw [hnext5] at hh
      exact hh
  · intro k hk u hu' x _
    have hu := hchain k u hu'
    interval_cases k
    · change Arm8L3Agree s1.memDomain u ms at hu
      have hb0' := hb0
      rw [BitVec.add_zero] at hb0'
      obtain ⟨b0, b1, b2, b3⟩ := hu.word hdom0 _ hb0' hb1 hb2 hb3
      rw [arm8Next_addSubImmediateS_zero u (BitVec.ofNat 5 sr) hsr5
        (by rw [hu.exc]; exact hexc0) b0 b1 b2 b3 (by rw [hu.pc]; exact hal)
        (by rw [hu.sctlr]; exact he0) (by rw [hu.pstate]; exact hel)]
    · change Arm8L3Agree s1.memDomain u (arm8AddCarryT1 ms sr) at hu
      obtain ⟨b0, b1, b2, b3⟩ := hu.word hdom1 _ ht1b0 ht1b1 ht1b2 ht1b3
      exact arm8Next_conditionalCompare_zero_mem u (BitVec.ofNat 5 rc)
        (by rw [hu.exc]; exact hexc0) b0 b1 b2 b3
        (by rw [hu.pc, arm8AddCarryT1_pc ms sr]; exact hal4a)
        (by rw [hu.sctlr]; exact he0) (by rw [hu.pstate]; exact hel) x
    · change Arm8L3Agree s1.memDomain u (arm8AddCarryT2 ms rc sr) at hu
      obtain ⟨b0, b1, b2, b3⟩ := hu.word hdom2 _ ht2b0 ht2b1 ht2b2 ht2b3
      exact arm8Next_addSubCarry_mem u true (BitVec.ofNat 5 sl) (BitVec.ofNat 5 rc)
        (BitVec.ofNat 5 d) hd5
        (by rw [hu.exc, arm8AddCarryT2_exc ms rc sr]; exact hexc0) b0 b1 b2 b3
        (by rw [hu.pc, arm8AddCarryT2_pc ms rc sr]; exact hal8a)
        (by rw [hu.sctlr, arm8AddCarryT2_sctlr ms rc sr]; exact he0)
        (by rw [hu.pstate, arm8AddCarryT2_el ms rc sr]; exact hel) x
    · change Arm8L3Agree s1.memDomain u (arm8AddCarryT3 ms d rc sl sr) at hu
      obtain ⟨b0, b1, b2, b3⟩ := hu.word hdom3 _ ht3b0 ht3b1 ht3b2 ht3b3
      exact arm8Next_moveWide_z_zero_mem u (BitVec.ofNat 5 sr) hsr5
        (by rw [hu.exc, arm8AddCarryT3_exc ms d rc sl sr]; exact hexc0) b0 b1 b2 b3
        (by rw [hu.pc, arm8AddCarryT3_pc ms d rc sl sr]; exact hal12a)
        (by rw [hu.sctlr, arm8AddCarryT3_sctlr ms d rc sl sr]; exact he0)
        (by rw [hu.pstate, arm8AddCarryT3_el ms d rc sl sr]; exact hel) x
    · change Arm8L3Agree s1.memDomain u (arm8AddCarryT4 ms d rc sl sr) at hu
      obtain ⟨b0, b1, b2, b3⟩ := hu.word hdom4 _ ht4b0 ht4b1 ht4b2 ht4b3
      exact arm8Next_addSubCarry_mem u false (31 : BitVec 5) (BitVec.ofNat 5 sr)
        (BitVec.ofNat 5 sr) hsr5
        (by rw [hu.exc, arm8AddCarryT4_exc ms d rc sl sr]; exact hexc0) b0 b1 b2 b3
        (by rw [hu.pc, arm8AddCarryT4_pc ms d rc sl sr]; exact hal16a)
        (by rw [hu.sctlr, arm8AddCarryT4_sctlr ms d rc sl sr]; exact he0)
        (by rw [hu.pstate, arm8AddCarryT4_el ms d rc sl sr]; exact hel) x
  · intro k h1 h2
    interval_cases k
    · exact hok1
    · exact hok2
    · exact hok3
    · exact hok4
  · intro k h1 h2
    interval_cases k
    · exact arm8AddCarryT1_pc ms sr
    · exact arm8AddCarryT2_pc ms rc sr
    · exact arm8AddCarryT3_pc ms d rc sl sr
    · exact arm8AddCarryT4_pc ms d rc sl sr
  · intro k h1 h2 x _
    interval_cases k
    · exact arm8AddCarryT1_mem ms sr x
    · exact arm8AddCarryT2_mem ms rc sr x
    · exact arm8AddCarryT3_mem ms d rc sl sr x
    · exact arm8AddCarryT4_mem ms d rc sl sr x

end Flapjack.Compiler.Encoders.Arm8.L3
