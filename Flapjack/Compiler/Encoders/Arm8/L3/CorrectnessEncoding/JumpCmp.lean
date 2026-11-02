import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Overflow
import Flapjack.Compiler.Encoders.Arm8.Machine.JumpCmpCase
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.BranchConditional

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# `JumpCmp`: the flag-setting compare instructions

`arm8_ast` lowers `JumpCmp` to a compare into `XZR` (`0x1Fw`) followed by a
`BranchConditional` on `cmp_cond cmp`.  The `is_test` forms emit
`LogicalShiftedRegister@64` with `LogicalOp_AND` and `S := T` (its opcode bits
are `0b11`); the ordering forms emit `AddSubShiftedRegister@64` with
`op := T` and `S := T`.

This module records the instruction-level `Encode`/`Decode`/`Run`/`Next` facts
for both compare shapes.  These are Flapjack case splits of the single HOL
theorem `arm8_encoder_correct` (`cakeml/compiler/encoders/arm8/
arm8_targetProofScript.sml`), so they carry no `@[hol]` tag of their own; the
HOL `JumpCmp` case is tracked on the assembling theorem.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-! ## The `is_test` compare: `ANDS` into `XZR` -/

/-- `Encode` of the `LogicalShiftedRegister@64` that `arm8_ast` emits for the
`is_test` comparisons: an `AND` with `S := T`, whose opcode bits are `0b11`. -/
theorem arm8Encode_logicalShiftedRegister_ands (rm rn rd : BitVec 5) :
    Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
        (0, (rm, (rn, rd)))))))))) =
      MachineCode.ARM8 (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd) := by
  rfl

/-- The rendered `Decode` inverts `arm8LogicalShiftedRegisterWord` when the
decoded opcode carries the set-flags bit. -/
theorem arm8Decode_logicalShiftedRegister_setflags (opc : LogicalOp) (opcbits : BitVec 2)
    (hdec : DecodeLogicalOp opcbits = (opc, true)) (invert : Bool) (rm rn rd : BitVec 5) :
    Decode (arm8LogicalShiftedRegisterWord opcbits invert .lsl 0 rm rn rd) =
      instruction.Data (Data.«LogicalShiftedRegister@64»
        ((1 : BitVec 64), (opc, (invert, (true, (ShiftType.lsl,
          (0, (rm, (rn, rd))))))))) := by
  simp only [arm8LogicalShiftedRegisterWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases invert <;>
    simp [holV2w_two, holV2w_two_zero, holV2w_five, arm8HolV2w_one_false,
      arm8HolV2w_one_true, arm8HolV2w_six_zero, hdec, DecodeShift, num2ShiftType,
      ShiftType2num]

/-- `DecodeLogicalOp` of the `ANDS` opcode bits is `LogicalOp_AND` with the
set-flags bit. -/
theorem arm8DecodeLogicalOp_ands :
    DecodeLogicalOp (3 : BitVec 2) = (.LogicalOp_AND, true) := by
  simp [DecodeLogicalOp]

/-- `Decode` of the `ANDS` word is the compare instruction. -/
theorem arm8Decode_logicalShiftedRegister_ands (rm rn rd : BitVec 5) :
    Decode (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd) =
      instruction.Data (Data.«LogicalShiftedRegister@64»
        ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
          (0, (rm, (rn, rd))))))))) :=
  arm8Decode_logicalShiftedRegister_setflags .LogicalOp_AND 3 arm8DecodeLogicalOp_ands false rm rn rd

/-- `Run` of the `ANDS` compare into `XZR`: the `AND` result sets `N` from its
most significant bit, `Z` from its zero-ness, and clears `C` and `V`; the
`XZR` destination discards the value. -/
theorem arm8Run_logicalShiftedRegister_ands_eq (rm rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
        (0, (rm, (rn, 31)))))))))) st =
      { st with
        PSTATE :=
          { st.PSTATE with
            N := BitVec.msb (X (TN := 64) rn st &&& X (TN := 64) rm st),
            Z := (X (TN := 64) rn st &&& X (TN := 64) rm st) == (0 : BitVec 64),
            C := false,
            V := false } } := by
  simp only [Run, «dfn'LogicalShiftedRegister», SetTheFlags, ShiftReg, ShiftValue,
    BitVec.shiftLeft_zero, «write'X», if_true, Bool.false_eq_true]
  rfl

/-- One `arm8Next` step on the `ANDS` compare word: the flags come from the
`AND`, the destination is `XZR`, and `PC` advances by four. -/
theorem arm8Next_logicalShiftedRegister_ands (ms : arm8_state) (rm rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := BitVec.msb (X (TN := 64) rn ms &&& X (TN := 64) rm ms),
            Z := (X (TN := 64) rn ms &&& X (TN := 64) rm ms) == (0 : BitVec 64),
            C := false,
            V := false } } := by
  let i : instruction := instruction.Data (Data.«LogicalShiftedRegister@64»
    ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl, (0, (rm, (rn, 31)))))))))
  have hdec : Decode (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31) = i := by
    dsimp only [i]
    exact arm8Decode_logicalShiftedRegister_ands rm rn 31
  have hrun := arm8Run_logicalShiftedRegister_ands_eq rm rn { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31)
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  rfl

/-! ## The ordering compare: `SUBS` into `XZR` -/

/-- Writing to `XZR` (`31`) leaves the state unchanged. -/
theorem arm8WriteX_xzr (s : arm8_state) (v : BitVec 64) :
    «write'X» (v, (31 : BitVec 5)) s = s := by
  simp [«write'X»]

/-- `Run` of the flag-setting `AddSubShiftedRegister@64` compare into `XZR`:
the subtraction `Rn - Rm` sets the flags from `AddWithCarry` and the `XZR`
destination discards the value. -/
theorem arm8Run_addSubShiftedRegister_setflags_xzr_eq (rm rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (true, (true, (ShiftType.lsl, (rm, (0, (rn, 31))))))))) st =
      { st with
        PSTATE :=
          { st.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.2.2.2 } } := by
  rw [arm8Run_addSubShiftedRegister_setflags]
  dsimp only
  rw [arm8WriteX_xzr]
  have hz : BitVec.toNat (0 : BitVec 6) = 0 := by decide
  simp only [SetTheFlags, ShiftReg, ShiftValue, if_true, hz, BitVec.shiftLeft_zero]

/-- One `arm8Next` step on the `SUBS` compare word: the flags come from
`Rn - Rm`, the destination is `XZR`, and `PC` advances by four. -/
theorem arm8Next_addSubShiftedRegister_setflags_xzr (ms : arm8_state) (rm rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.2.2.2 } } := by
  let i : instruction := instruction.Data (Data.«AddSubShiftedRegister@64»
    ((1 : BitVec 64), (true, (true, (ShiftType.lsl, (rm, (0, (rn, 31))))))))
  have hdec : Decode (arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31) = i := by
    dsimp only [i]
    exact arm8Decode_addSubShiftedRegister true true rm 0 rn 31
  have hrun := arm8Run_addSubShiftedRegister_setflags_xzr_eq rm rn { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31)
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  rfl

/-! ## The flag semantics of the two compare shapes

`ConditionHolds` reads the four flags through the rendered `ConditionTest`
table.  The arithmetic facts about `AddWithCarry`'s flags at 64 bits are the
machine model's `jumpCmp_flags_*` lemmas, reached through
`arm8AddWithCarry_machine`; this keeps the L3 case theorem on the same
subtraction semantics the machine model already proved against `BitVec.slt`. -/

/-- Boolean equality over a lawful `BEq` is decided equality. -/
theorem arm8Beq_eq_decide {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]

/-- Negated decided truth is decided falsity. -/
theorem arm8NotDecide_eq_decide_ne {p : Prop} [Decidable p] [Decidable ¬p] :
    (!decide p) = decide (¬p) := (decide_not (p := p)).symm

/-- The most significant bit of a sixty-four-bit word is bit 63. -/
theorem arm8GetMsbD_zero_64 (r : BitVec 64) : r.getMsbD 0 = r.getLsbD 63 := by
  rw [BitVec.getMsbD_eq_getLsbD]
  simp

/-- The rendered `AddWithCarry` at 64 bits is the machine model's
`addWithCarry`. -/
theorem arm8AddWithCarry_machine (x y : BitVec 64) (c : Bool) :
    AddWithCarry (TN := 64) (x, (y, c)) = addWithCarry x y c := by
  simp only [AddWithCarry, addWithCarry, BitVec.msb, arm8GetMsbD_zero_64,
    arm8Beq_eq_decide, arm8NotDecide_eq_decide_ne]
  rfl

/-- The `C` flag of the `SUBS` compare is "not below" (unsigned). -/
theorem arm8SubFlags_c (x y : BitVec 64) :
    (AddWithCarry (TN := 64) (x, (~~~y, true))).2.2.2.1 = !(x.ult y) := by
  rw [arm8AddWithCarry_machine]
  exact jumpCmp_flags_c x y

/-- The `Z` flag of the `SUBS` compare is equality. -/
theorem arm8SubFlags_z (x y : BitVec 64) :
    (AddWithCarry (TN := 64) (x, (~~~y, true))).2.2.1 = decide (x = y) := by
  rw [arm8AddWithCarry_machine]
  exact jumpCmp_flags_z x y

/-- The `N`/`V` pair of the `SUBS` compare is signed less-than. -/
theorem arm8SubFlags_slt (x y : BitVec 64) :
    ((AddWithCarry (TN := 64) (x, (~~~y, true))).2.1 !=
      (AddWithCarry (TN := 64) (x, (~~~y, true))).2.2.2.2) = x.slt y := by
  rw [arm8AddWithCarry_machine]
  exact jumpCmp_flags_slt x y

/-- The rendered `ConditionTest` table on the condition codes `cmp_cond`
emits, over an arbitrary flag tuple. -/
theorem arm8ConditionTest_cmpCond (cmp : Cmp) (f : Bool × (Bool × (Bool × Bool))) :
    ConditionTest (arm8CmpCond cmp, f) =
      (match cmp with
        | .equal => f.2.1
        | .less => f.1 != f.2.2.2
        | .lower => !f.2.2.1
        | .test => f.2.1
        | .notEqual => !f.2.1
        | .notLess => f.1 == f.2.2.2
        | .notLower => f.2.2.1
        | .notTest => !f.2.1) := by
  obtain ⟨n, z, c, v⟩ := f
  cases cmp <;>
    simp only [arm8CmpCond, ConditionTest, Flapjack.RiscV.L3.holWordExtract] <;> rfl

/-- The condition code of a non-`test` comparison against the flags of
`AddWithCarry x (~~~y) true`, i.e. of the subtraction `x - y`. -/
theorem arm8SubCmp_semantics (cmp : Cmp) (x y : BitVec 64) (hNT : isTest cmp = false) :
    ConditionTest (arm8CmpCond cmp, (AddWithCarry (TN := 64) (x, (~~~y, true))).2) =
      wordCmpHOL cmp x y := by
  rw [arm8ConditionTest_cmpCond]
  cases cmp
  case equal =>
    simp only [wordCmpHOL, arm8SubFlags_z, arm8Beq_eq_decide]
  case less =>
    simp only [wordCmpHOL, arm8SubFlags_slt, jumpCmp_holAsmSignedLess_eq]
  case lower =>
    simp only [wordCmpHOL, arm8SubFlags_c, Bool.not_not, BitVec.ult_eq_decide_lt]
  case test => simp [isTest] at hNT
  case notEqual =>
    simp only [wordCmpHOL, arm8SubFlags_z, arm8Beq_eq_decide]
  case notLower =>
    simp only [wordCmpHOL, arm8SubFlags_c, BitVec.ult_eq_decide_lt]
  case notLess =>
    have h := arm8SubFlags_slt x y
    simp only [wordCmpHOL, jumpCmp_holAsmSignedLess_eq]
    rw [← h]
    simp only [bne, Bool.not_not]
  case notTest => simp [isTest] at hNT

/-- The condition code of a `test`/`notTest` comparison against the flags of
the `ANDS` compare, i.e. of `x &&& y`. -/
theorem arm8AndCmp_semantics (cmp : Cmp) (x y : BitVec 64) (hT : isTest cmp = true) :
    ConditionTest (arm8CmpCond cmp,
      (BitVec.msb (x &&& y), ((x &&& y) == (0 : BitVec 64), (false, false)))) =
      wordCmpHOL cmp x y := by
  rw [arm8ConditionTest_cmpCond]
  cases cmp
  case equal => simp [isTest] at hT
  case less => simp [isTest] at hT
  case lower => simp [isTest] at hT
  case test => simp only [wordCmpHOL, AndOp.and]; rfl
  case notEqual => simp [isTest] at hT
  case notLess => simp [isTest] at hT
  case notLower => simp [isTest] at hT
  case notTest => simp only [wordCmpHOL, AndOp.and, bne]; rfl

/-! ## The `JumpCmp` lowering: instruction list, encoding and offsets -/

/-- `JumpCmp` with a register operand lowers to the flag-setting compare and
the conditional branch on `cmp_cond`. -/
theorem arm8Ast_jumpCmp_reg (cmp : Cmp) (r t : Nat) (a : BitVec 64) :
    arm8Ast (.jumpCmp cmp r (.reg t) a) =
      [.Data (if isTest cmp then
                .«LogicalShiftedRegister@64»
                  (1, .LogicalOp_AND, false, true, .lsl, 0, t, r, 31)
              else
                .«AddSubShiftedRegister@64»
                  (1, true, true, .lsl, t, 0, r, 31)),
       .Branch (.BranchConditional (a - 4, arm8CmpCond cmp))] := rfl

/-- `JumpCmp` with an immediate operand lowers to the flag-setting compare and
the conditional branch on `cmp_cond`. -/
theorem arm8Ast_jumpCmp_imm (cmp : Cmp) (r : Nat) (v a : BitVec 64) :
    arm8Ast (.jumpCmp cmp r (.imm v) a) =
      [.Data (if isTest cmp then
                .«LogicalImmediate@64» (1, .LogicalOp_AND, true, v, r, 31)
              else
                .«AddSubImmediate@64» (1, true, true, v, r, 31)),
       .Branch (.BranchConditional (a - 4, arm8CmpCond cmp))] := rfl

/-- The encoded bytes of the register `JumpCmp` lowering. -/
theorem arm8Enc_jumpCmp_reg (cmp : Cmp) (r t : Nat) (a : BitVec 64) :
    arm8Enc (.jumpCmp cmp r (.reg t) a) =
      arm8Encode (.Data (if isTest cmp then
                  .«LogicalShiftedRegister@64»
                    (1, .LogicalOp_AND, false, true, .lsl, 0, t, r, 31)
                else
                  .«AddSubShiftedRegister@64»
                    (1, true, true, .lsl, t, 0, r, 31))) ++
      arm8Encode (.Branch (.BranchConditional (a - 4, arm8CmpCond cmp))) := by
  simp [arm8Enc, arm8Ast_jumpCmp_reg]

/-- The encoded bytes of the immediate `JumpCmp` lowering. -/
theorem arm8Enc_jumpCmp_imm (cmp : Cmp) (r : Nat) (v a : BitVec 64) :
    arm8Enc (.jumpCmp cmp r (.imm v) a) =
      arm8Encode (.Data (if isTest cmp then
                  .«LogicalImmediate@64» (1, .LogicalOp_AND, true, v, r, 31)
                else
                  .«AddSubImmediate@64» (1, true, true, v, r, 31))) ++
      arm8Encode (.Branch (.BranchConditional (a - 4, arm8CmpCond cmp))) := by
  simp [arm8Enc, arm8Ast_jumpCmp_imm]

/-- The register `JumpCmp` lowering encodes to eight bytes. -/
theorem arm8Enc_jumpCmp_reg_length (cmp : Cmp) (r t : Nat) (a : BitVec 64) :
    (arm8Enc (.jumpCmp cmp r (.reg t) a)).length = 8 := by
  rw [arm8Enc_jumpCmp_reg, List.length_append, arm8Encode_length, arm8Encode_length]

/-- The immediate `JumpCmp` lowering encodes to eight bytes. -/
theorem arm8Enc_jumpCmp_imm_length (cmp : Cmp) (r : Nat) (v a : BitVec 64) :
    (arm8Enc (.jumpCmp cmp r (.imm v) a)).length = 8 := by
  rw [arm8Enc_jumpCmp_imm, List.length_append, arm8Encode_length, arm8Encode_length]

/-- The `cjump` offset window of `arm8ConfigL3` gives the conditional-branch
encoder's twenty-one-bit range and the four-byte alignment. -/
theorem arm8CjumpOk_of_asm (cmp : Cmp) (r : Nat) (ri : HolRegImm 64) (a : BitVec 64)
    (h : asmOkExact (.jumpCmp cmp r ri a) arm8ConfigL3 = true) :
    (-1048572 : Int) ≤ a.toInt ∧ a.toInt ≤ 1048579 ∧ a.toNat % 4 = 0 := by
  simp only [asmOkExact, arm8ConfigL3, asmCjumpOffsetOkExact, asmOffsetOkExact,
    Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlo, hhi⟩, hal⟩, _⟩ := h
  have hlo' := arm8OfDecideTrue _ hlo
  have hhi' := arm8OfDecideTrue _ hhi
  have hmod : a.toNat % 4 = 0 := by simpa [asmAligned] using hal
  refine ⟨hlo', ?_, hmod⟩
  simpa using hhi'

/-- The encoded branch offset `a - 4` is in the signed twenty-one-bit range and
four-byte aligned when the target `a` is in the `cjump` window. -/
theorem arm8CjumpOffsetOk (a : BitVec 64)
    (hlo : (-1048572 : Int) ≤ a.toInt) (hhi : a.toInt ≤ 1048579)
    (hmod : a.toNat % 4 = 0) :
    (-(2 ^ 20 : Int) ≤ (a - 4).toInt ∧ (a - 4).toInt ≤ 2 ^ 20 - 1) ∧
      (a - 4).toNat % 4 = 0 := by
  have hInt : (a - 4).toInt = a.toInt - 4 := by
    rw [BitVec.toInt_sub]
    have h4 : BitVec.toInt (4 : BitVec 64) = 4 := by decide
    rw [h4]
    apply (Int.bmod_eq_iff (by norm_num : (0 : Nat) < 2 ^ 64)).2
    refine ⟨?_, ?_, ⟨0, by norm_num⟩⟩ <;> norm_num <;> omega
  have hNat : (a - 4).toNat % 4 = 0 := by
    rw [BitVec.toNat_sub]
    have h4 : (4 : BitVec 64).toNat = 4 := by decide
    rw [h4]
    omega
  exact ⟨⟨by rw [hInt]; omega, by rw [hInt]; omega⟩, hNat⟩

/-- The four encoded bytes of the `ANDS` compare word. -/
theorem arm8EncodeBytes_logicalShiftedRegister_ands (rm rn rd : BitVec 5) :
    arm8Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
        (0, (rm, (rn, rd)))))))))) =
      [BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_logicalShiftedRegister_ands]

/-- The `asmCmpOkExact` conjuncts of a register `JumpCmp`: both the source and
the right operand are valid registers. -/
theorem arm8CmpOk_of_asm (cmp : Cmp) (r t : Nat) (a : BitVec 64)
    (h : asmOkExact (.jumpCmp cmp r (.reg t) a) arm8ConfigL3 = true) :
    r < 32 ∧ arm8ConfigL3.avoidRegs.contains r = false ∧ r ≠ 31 ∧
      t < 32 ∧ arm8ConfigL3.avoidRegs.contains t = false ∧ t ≠ 31 := by
  simp only [asmOkExact, arm8ConfigL3, asmCmpOkExact, asmRegImmOkExact,
    Bool.and_eq_true] at h
  obtain ⟨_, hs, hr⟩ := h
  obtain ⟨h1, h2, h3⟩ := regOk_of_asmL3 hs
  obtain ⟨h4, h5, h6⟩ := regOk_of_asmL3 hr
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The eight encoded bytes of a `test` register `JumpCmp` lowering: the `ANDS`
compare word followed by the conditional-branch word. -/
theorem arm8Enc_jumpCmp_reg_test (cmp : Cmp) (r t : Nat) (a : BitVec 64)
    (hT : isTest cmp = true)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 (a - 4) ++ BitVec.ofNat 2 0)) = a - 4) :
    arm8Enc (.jumpCmp cmp r (.reg t) a) =
      [BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
          (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 0).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
          (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 8).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
          (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 16).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
          (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 24).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 24).toNat)] := by
  rw [arm8Enc_jumpCmp_reg]
  rw [if_pos hT]
  rw [arm8EncodeBytes_logicalShiftedRegister_ands,
    arm8EncodeBytes_branchConditional _ _ hround]
  rfl

/-- The eight encoded bytes of an ordering register `JumpCmp` lowering: the
`SUBS` compare word followed by the conditional-branch word. -/
theorem arm8Enc_jumpCmp_reg_ord (cmp : Cmp) (r t : Nat) (a : BitVec 64)
    (hNT : isTest cmp = false)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 (a - 4) ++ BitVec.ofNat 2 0)) = a - 4) :
    arm8Enc (.jumpCmp cmp r (.reg t) a) =
      [BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
          (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 0).toNat),
       BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
          (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 8).toNat),
       BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
          (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 16).toNat),
       BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
          (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 24).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
          (arm8CmpCond cmp) >>> 24).toNat)] := by
  rw [arm8Enc_jumpCmp_reg]
  rw [if_neg (by simp [hNT])]
  rw [arm8EncodeBytes_addSubShiftedRegister,
    arm8EncodeBytes_branchConditional _ _ hround]
  rfl

end Flapjack.Compiler.Encoders.Arm8.L3
