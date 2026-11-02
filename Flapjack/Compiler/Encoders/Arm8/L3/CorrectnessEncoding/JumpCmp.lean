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

/-! ## Agreement lemmas for the two `JumpCmp` steps -/

/-- Applying `arm8Next` to two states that agree on `d` and carry the `ANDS`
compare word gives states that still agree. -/
theorem arm8Next_logicalShiftedRegister_ands_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rm rn : BitVec 5)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 24).toNat)) :
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
  have hs0 : s.MEM s.PC = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8
      ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_logicalShiftedRegister_ands s rm rn hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_logicalShiftedRegister_ands t rm rn hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hrn : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hrm : X (TN := 64) rm s = X (TN := 64) rm t := arm8X_congr_or_zero h rm
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · exact h.reg
  · simp only [h.pstate, hrn, hrm]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    exact h.mem a ha

/-- Applying `arm8Next` to two states that agree on `d` and carry the `SUBS`
compare word into `XZR` gives states that still agree. -/
theorem arm8Next_addSubShiftedRegister_setflags_xzr_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rm rn : BitVec 5)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 24).toNat)) :
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
  have hs0 : s.MEM s.PC = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8
      ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_addSubShiftedRegister_setflags_xzr s rm rn hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_addSubShiftedRegister_setflags_xzr t rm rn hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  have hrn : X (TN := 64) rn s = X (TN := 64) rn t := arm8X_congr_or_zero h rn
  have hrm : X (TN := 64) rm s = X (TN := 64) rm t := arm8X_congr_or_zero h rm
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · exact h.reg
  · simp only [h.pstate, hrn, hrm]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    exact h.mem a ha

/-- One `arm8Next` step on the conditional-branch word, as a state equation. -/
theorem arm8Next_branchConditional' (ms : arm8_state) (l : BitVec 64) (cd : BitVec 4)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    arm8Next ms =
      (if ConditionHolds cd ms then
        { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l }
       else { ms with branch_hint := none, PC := ms.PC + 4 }) := by
  unfold arm8Next
  rw [arm8Next_branchConditional ms l cd hround hexc0 h0 h1 h2 h3 hal he0 hel htbi1 htbi0]
  rfl

/-- Applying `arm8Next` to two states that agree on `d` and carry the same
conditional-branch word gives states that still agree. -/
theorem arm8Next_branchConditional_agree (d : BitVec 64 → Prop)
    (s t : arm8_state) (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (l : BitVec 64) (cd : BitVec 4)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 l ++ BitVec.ofNat 2 0)) = l)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, htbi1t, htbi0t, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa [← h.pc] using (holAligned_iff 2 s.PC).mp halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 t.PC).mp halignt
  have hs0 : s.MEM s.PC =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_branchConditional' s l cd hround hexc0 hs0 hs1 hs2 hs3 hal he0 hel htbi1 htbi0
  have htt := arm8Next_branchConditional' t l cd hround hexc0t hb0 hb1 hb2 hb3 halt he0t helt htbi1t htbi0t
  rw [hss, htt]
  by_cases hc : ConditionHolds cd s = true
  · have hct : ConditionHolds cd t = true := by
      rw [← arm8ConditionHolds_congr cd h.pstate]; exact hc
    rw [if_pos hc, if_pos hct]
    exact ⟨by rw [h.pc], h.reg, h.pstate, h.sctlr, h.tcr, h.exc, fun a ha => h.mem a ha⟩
  · have hcs : ConditionHolds cd s = false := Bool.eq_false_iff.mpr hc
    have hct : ConditionHolds cd t = false := by
      rw [← arm8ConditionHolds_congr cd h.pstate]; exact hcs
    rw [if_neg hc, if_neg (by rw [hct]; simp)]
    exact ⟨by rw [h.pc], h.reg, h.pstate, h.sctlr, h.tcr, h.exc, fun a ha => h.mem a ha⟩

/-- The conditional-branch step leaves memory unchanged. -/
theorem arm8Next_branchConditional_mem (ms : arm8_state) (l : BitVec 64) (cd : BitVec 4)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    ∀ x, (arm8Next ms).MEM x = ms.MEM x := by
  rw [arm8Next_branchConditional' ms l cd hround hexc0 h0 h1 h2 h3 hal he0 hel htbi1 htbi0]
  intro x
  split <;> rfl

/-- The register `JumpCmp` constructor of `encoder_correct arm8TargetL3`: the
flag-setting compare at `PC` followed by the conditional branch at `PC + 4`,
two `arm8Next` steps. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_jumpCmp_reg (cmp : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.jumpCmp cmp r (.reg t) a) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.jumpCmp cmp r (.reg t) a) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ x, s1.memDomain x → ms.MEM x = s1.mem x at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  obtain ⟨hsrc, hsrcav, hsrc31, hrt, hrtav, hrt31⟩ := arm8CmpOk_of_asm cmp r t a hs.2.2.2.2.2.2
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  obtain ⟨hlo, hhi, hmod⟩ := arm8CjumpOk_of_asm cmp r (.reg t) a hs.2.2.2.2.2.2
  obtain ⟨⟨hOffLo, hOffHi⟩, hOffMod⟩ := arm8CjumpOffsetOk a hlo hhi hmod
  have hround := arm8BranchCondRoundtrip (a - 4) hOffLo hOffHi hOffMod
  have hsrcv : ms.REG (BitVec.ofNat 5 r) = s1.regs r :=
    hreg r ⟨by simpa [arm8ConfigL3] using hsrc, hsrcav⟩
  have hrtv : ms.REG (BitVec.ofNat 5 t) = s1.regs t :=
    hreg t ⟨by simpa [arm8ConfigL3] using hrt, hrtav⟩
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.jumpCmp cmp r (.reg t) a)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hlen : (arm8Enc (.jumpCmp cmp r (.reg t) a)).length = 8 :=
    arm8Enc_jumpCmp_reg_length cmp r t a
  have hbyte (i : Nat) (hi : i < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) = (arm8Enc (.jumpCmp cmp r (.reg t) a)).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [hlen]; exact hi)
  let T1 : arm8_state :=
    if isTest cmp then
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := BitVec.msb (X (TN := 64) (BitVec.ofNat 5 r) ms &&& X (TN := 64) (BitVec.ofNat 5 t) ms),
            Z := (X (TN := 64) (BitVec.ofNat 5 r) ms &&& X (TN := 64) (BitVec.ofNat 5 t) ms) == (0 : BitVec 64),
            C := false,
            V := false } }
    else
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) (BitVec.ofNat 5 r) ms,
              (~~~X (TN := 64) (BitVec.ofNat 5 t) ms, true))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) (BitVec.ofNat 5 r) ms,
              (~~~X (TN := 64) (BitVec.ofNat 5 t) ms, true))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) (BitVec.ofNat 5 r) ms,
              (~~~X (TN := 64) (BitVec.ofNat 5 t) ms, true))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) (BitVec.ofNat 5 r) ms,
              (~~~X (TN := 64) (BitVec.ofNat 5 t) ms, true))).2.2.2.2 } }
  have hT1pc : T1.PC = ms.PC + 4 := by unfold T1; split <;> rfl
  have hT1mem : ∀ x, T1.MEM x = ms.MEM x := by intro x; unfold T1; split <;> rfl
  have hT1reg : T1.REG = ms.REG := by unfold T1; split <;> rfl
  have hT1exc : T1.exception = exception.NoException := by unfold T1; split <;> exact hexc0
  have hT1sctlr : T1.SCTLR_EL1 = ms.SCTLR_EL1 := by unfold T1; split <;> rfl
  have hT1tcr : T1.TCR_EL1 = ms.TCR_EL1 := by unfold T1; split <;> rfl
  have hT1el : T1.PSTATE.EL = ms.PSTATE.EL := by unfold T1; split <;> rfl
  have h4 : holAligned 2 (ms.PC + 4) = true := by
    rw [(alignedAddSub 2 ms.PC 4 (by rw [holAligned_iff]; decide)).1]
    exact halign
  have hal4 : Aligned (TN := 64) (T1.PC, 4) = true := by
    rw [hT1pc]
    exact aligned_of_holAligned (ms.PC + 4) h4
  have hT1ok : arm8Ok T1 = true := by
    rw [arm8Ok_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold T1; split <;> exact hel
    · unfold T1; split <;> exact he0
    · unfold T1; split <;> exact hsa0
    · unfold T1; split <;> exact htbi1
    · unfold T1; split <;> exact htbi0
    · unfold T1; split <;> exact hexc0
    · rw [hT1pc]; exact h4
  have hn1 : arm8Next ms = T1 := by
    by_cases htest : isTest cmp = true
    · dsimp only [T1]; rw [if_pos htest]
      rw [arm8Enc_jumpCmp_reg_test cmp r t a htest hround] at hbyte
      have hb0 : ms.MEM ms.PC = BitVec.ofNat 8
          ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
            (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 0).toNat) := by
        simpa using hbyte 0 (by norm_num)
      have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8
          ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
            (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 8).toNat) := by
        simpa using hbyte 1 (by norm_num)
      have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8
          ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
            (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 16).toNat) := by
        simpa using hbyte 2 (by norm_num)
      have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8
          ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0
            (BitVec.ofNat 5 t) (BitVec.ofNat 5 r) 31 >>> 24).toNat) := by
        simpa using hbyte 3 (by norm_num)
      exact arm8Next_logicalShiftedRegister_ands ms (BitVec.ofNat 5 t) (BitVec.ofNat 5 r)
        hexc0 hb0 hb1 hb2 hb3 hal he0 hel
    · have hNT : isTest cmp = false := Bool.eq_false_iff.mpr htest
      dsimp only [T1]; rw [if_neg htest]
      rw [arm8Enc_jumpCmp_reg_ord cmp r t a hNT hround] at hbyte
      have hb0 : ms.MEM ms.PC = BitVec.ofNat 8
          ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
            (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 0).toNat) := by
        simpa using hbyte 0 (by norm_num)
      have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8
          ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
            (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 8).toNat) := by
        simpa using hbyte 1 (by norm_num)
      have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8
          ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
            (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 16).toNat) := by
        simpa using hbyte 2 (by norm_num)
      have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8
          ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl
            (BitVec.ofNat 5 t) 0 (BitVec.ofNat 5 r) 31 >>> 24).toNat) := by
        simpa using hbyte 3 (by norm_num)
      exact arm8Next_addSubShiftedRegister_setflags_xzr ms (BitVec.ofNat 5 t) (BitVec.ofNat 5 r)
        hexc0 hb0 hb1 hb2 hb3 hal he0 hel
  have hcond : ConditionHolds (arm8CmpCond cmp) T1 =
      wordCmpHOL cmp (ms.REG (BitVec.ofNat 5 r)) (ms.REG (BitVec.ofNat 5 t)) := by
    by_cases htest : isTest cmp = true
    · dsimp only [T1]; rw [if_pos htest]
      unfold ConditionHolds
      rw [arm8X_of_valid ms hsrc31 hsrc, arm8X_of_valid ms hrt31 hrt]
      exact arm8AndCmp_semantics cmp _ _ htest
    · have hNT : isTest cmp = false := Bool.eq_false_iff.mpr htest
      dsimp only [T1]; rw [if_neg htest]
      unfold ConditionHolds
      rw [arm8X_of_valid ms hsrc31 hsrc, arm8X_of_valid ms hrt31 hrt]
      exact arm8SubCmp_semantics cmp _ _ hNT
  have hbr : (arm8Enc (.jumpCmp cmp r (.reg t) a)).getD 4 0 =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
        (arm8CmpCond cmp) >>> 0).toNat) := by
    by_cases htest : isTest cmp = true
    · rw [arm8Enc_jumpCmp_reg_test cmp r t a htest hround]; simp
    · rw [arm8Enc_jumpCmp_reg_ord cmp r t a (Bool.eq_false_iff.mpr htest) hround]; simp
  have hbr1 : (arm8Enc (.jumpCmp cmp r (.reg t) a)).getD 5 0 =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
        (arm8CmpCond cmp) >>> 8).toNat) := by
    by_cases htest : isTest cmp = true
    · rw [arm8Enc_jumpCmp_reg_test cmp r t a htest hround]; simp
    · rw [arm8Enc_jumpCmp_reg_ord cmp r t a (Bool.eq_false_iff.mpr htest) hround]; simp
  have hbr2 : (arm8Enc (.jumpCmp cmp r (.reg t) a)).getD 6 0 =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
        (arm8CmpCond cmp) >>> 16).toNat) := by
    by_cases htest : isTest cmp = true
    · rw [arm8Enc_jumpCmp_reg_test cmp r t a htest hround]; simp
    · rw [arm8Enc_jumpCmp_reg_ord cmp r t a (Bool.eq_false_iff.mpr htest) hround]; simp
  have hbr3 : (arm8Enc (.jumpCmp cmp r (.reg t) a)).getD 7 0 =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 (a - 4))
        (arm8CmpCond cmp) >>> 24).toNat) := by
    by_cases htest : isTest cmp = true
    · rw [arm8Enc_jumpCmp_reg_test cmp r t a htest hround]; simp
    · rw [arm8Enc_jumpCmp_reg_ord cmp r t a (Bool.eq_false_iff.mpr htest) hround]; simp
  have hbB0 : T1.MEM T1.PC = BitVec.ofNat 8 ((arm8BranchCondWord
      (holWordExtract 19 20 2 (a - 4)) (arm8CmpCond cmp) >>> 0).toNat) := by
    rw [hT1mem, hT1pc, ← hbr]
    exact hbyte 4 (by norm_num)
  have hbB1 : T1.MEM (T1.PC + 1) = BitVec.ofNat 8 ((arm8BranchCondWord
      (holWordExtract 19 20 2 (a - 4)) (arm8CmpCond cmp) >>> 8).toNat) := by
    rw [hT1mem, hT1pc, BitVec.add_assoc, ← hbr1]
    exact hbyte 5 (by norm_num)
  have hbB2 : T1.MEM (T1.PC + 2) = BitVec.ofNat 8 ((arm8BranchCondWord
      (holWordExtract 19 20 2 (a - 4)) (arm8CmpCond cmp) >>> 16).toNat) := by
    rw [hT1mem, hT1pc, BitVec.add_assoc, ← hbr2]
    exact hbyte 6 (by norm_num)
  have hbB3 : T1.MEM (T1.PC + 3) = BitVec.ofNat 8 ((arm8BranchCondWord
      (holWordExtract 19 20 2 (a - 4)) (arm8CmpCond cmp) >>> 24).toNat) := by
    rw [hT1mem, hT1pc, BitVec.add_assoc, ← hbr3]
    exact hbyte 7 (by norm_num)
  let T2 : arm8_state :=
    if ConditionHolds (arm8CmpCond cmp) T1 then
      { T1 with branch_hint := some .BranchType_JMP, PC := T1.PC + (a - 4) }
    else { T1 with branch_hint := none, PC := T1.PC + 4 }
  have hT2mem : ∀ x, T2.MEM x = T1.MEM x := by intro x; unfold T2; split <;> rfl
  have hT2reg : T2.REG = T1.REG := by unfold T2; split <;> rfl
  have hn2 : arm8Next T1 = T2 := by
    unfold T2
    exact arm8Next_branchConditional' T1 (a - 4) (arm8CmpCond cmp) hround hT1exc
      hbB0 hbB1 hbB2 hbB3 hal4
      (by rw [hT1sctlr]; exact he0) (by rw [hT1el]; exact hel)
      (by rw [hT1tcr]; exact htbi1) (by rw [hT1tcr]; exact htbi0)
  have hs2 : s2 = (if wordCmpHOL cmp (Flapjack.Compiler.Encoders.AsmSem.readReg r s1)
      (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1) then
      jumpToOffset a s1 else updPc (s1.pc + BitVec.ofNat 64 8) s1) := by
    have hupd := hs.2.2.2.2.1
    simp only [arm8ConfigL3] at hupd
    rw [hlen] at hupd
    rw [← hupd]
    simp [asmUpd]
  have hreadReg : Flapjack.Compiler.Encoders.AsmSem.readReg r s1 = s1.regs r := by
    simp [Flapjack.Compiler.Encoders.AsmSem.readReg]
  have hregImm : Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1 = s1.regs t := by
    simp [Flapjack.Compiler.Encoders.AsmSem.regImm, Flapjack.Compiler.Encoders.AsmSem.readReg]
  have hw : wordCmpHOL cmp (Flapjack.Compiler.Encoders.AsmSem.readReg r s1)
      (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1) =
      ConditionHolds (arm8CmpCond cmp) T1 := by
    rw [hreadReg, hregImm, ← hsrcv, ← hrtv, ← hcond]
  have hcode : allPcs 8 s1.pc 0 ⊆ s1.memDomain := by
    have h0' := bytesInMemory_allPcs (arm8Enc (.jumpCmp cmp r (.reg t) a)) s1.pc s1.mem
      s1.memDomain 0 hb
    rw [hlen] at h0'
    exact h0'
  have hdom8 : ∀ j, j < 8 → s1.memDomain (s1.pc + BitVec.ofNat 64 j) := by
    intro j hj
    exact hdom j (by rw [hlen]; exact hj)
  have hdomT1 : ∀ j, j < 4 → s1.memDomain (T1.PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : T1.PC + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j) := by
      rw [hT1pc]
      rw [hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom8 (4 + j) (by omega)
  refine ⟨1, ?_⟩
  intro env henv
  dsimp only
  simp only [arm8ConfigL3, hlen]
  have hagree : ∀ k x, Arm8L3Agree s1.memDomain (env k x) x :=
    fun k x => (arm8Proj_eq_iff s1.memDomain _ _).mp (henv k x)
  have a1 : Arm8L3Agree s1.memDomain (env 0 (arm8Next ms)) T1 := by
    rw [hn1]; exact hagree 0 _
  have a2 : Arm8L3Agree s1.memDomain (arm8Next (env 0 (arm8Next ms))) T2 := by
    have hh := arm8Next_branchConditional_agree s1.memDomain (env 0 (arm8Next ms)) T1 a1
      (by rw [arm8Ok_congr a1]; exact hT1ok) (a - 4) (arm8CmpCond cmp) hround hdomT1
      hbB0 hbB1 hbB2 hbB3
    rw [hn2] at hh
    exact hh
  have a2' : Arm8L3Agree s1.memDomain (env 1 (arm8Next (env 0 (arm8Next ms)))) T2 :=
    (hagree 1 (arm8Next (env 0 (arm8Next ms)))).trans a2
  have hP1 : arm8Ok (env 0 (arm8Next ms)) = true ∧
      (∀ pc, pc ∈ allPcs 8 s1.pc 0 → (env 0 (arm8Next ms)).MEM pc = ms.MEM pc) ∧
      (env 0 (arm8Next ms)).PC ∈ allPcs 8 s1.pc 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [arm8Ok_congr a1]; exact hT1ok
    · intro pc hpc'
      rw [a1.mem pc (hcode hpc'), hT1mem]
    · rw [a1.pc, hT1pc, hpc]
      simpa using mem_allPcs_eight_l3 s1.pc 1 (by norm_num)
  have hu1mem : ∀ x, (arm8Next (env 0 (arm8Next ms))).MEM x = (env 0 (arm8Next ms)).MEM x := by
    intro x
    have hh := arm8Next_branchConditional_mem (env 0 (arm8Next ms)) (a - 4) (arm8CmpCond cmp)
      hround (by rw [a1.exc]; exact hT1exc)
      (by rw [a1.pc, a1.mem T1.PC (by simpa using hdomT1 0 (by omega))]; exact hbB0)
      (by rw [a1.pc, a1.mem (T1.PC + 1) (by simpa using hdomT1 1 (by omega))]; exact hbB1)
      (by rw [a1.pc, a1.mem (T1.PC + 2) (by simpa using hdomT1 2 (by omega))]; exact hbB2)
      (by rw [a1.pc, a1.mem (T1.PC + 3) (by simpa using hdomT1 3 (by omega))]; exact hbB3)
      (by rw [a1.pc]; exact hal4) (by rw [a1.sctlr, hT1sctlr]; exact he0)
      (by rw [a1.pstate, hT1el]; exact hel)
      (by rw [a1.tcr, hT1tcr]; exact htbi1) (by rw [a1.tcr, hT1tcr]; exact htbi0) x
    exact hh
  have hs2dom : s2.memDomain = s1.memDomain := by
    by_cases hc : ConditionHolds (arm8CmpCond cmp) T1 = true
    · have hwt : wordCmpHOL cmp (Flapjack.Compiler.Encoders.AsmSem.readReg r s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1) = true := by rw [hw, hc]
      rw [hs2, if_pos hwt]; simp [jumpToOffset, updPc]
    · have hcs : ConditionHolds (arm8CmpCond cmp) T1 = false := Bool.eq_false_iff.mpr hc
      have hwf : wordCmpHOL cmp (Flapjack.Compiler.Encoders.AsmSem.readReg r s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1) = false := by rw [hw, hcs]
      rw [hs2, if_neg (by rw [hwf]; simp)]; simp [updPc]
  have hq : targetStateRel arm8TargetL3 s2 T2 := by
    by_cases hc : ConditionHolds (arm8CmpCond cmp) T1 = true
    · have hwt : wordCmpHOL cmp (Flapjack.Compiler.Encoders.AsmSem.readReg r s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1) = true := by rw [hw, hc]
      have hs2pc : s2.pc = s1.pc + a := by
        rw [hs2, if_pos hwt]; simp [jumpToOffset, updPc]
      have hs2mem : ∀ x, s2.mem x = s1.mem x := by
        rw [hs2, if_pos hwt]; intro x; simp [jumpToOffset, updPc]
      have hs2dom : s2.memDomain = s1.memDomain := by
        rw [hs2, if_pos hwt]; simp [jumpToOffset, updPc]
      have hs2regs : ∀ k, s2.regs k = s1.regs k := by
        rw [hs2, if_pos hwt]; intro k; simp [jumpToOffset, updPc]
      have hT2pc : T2.PC = ms.PC + a := by
        unfold T2; rw [if_pos hc]
        show T1.PC + (a - 4) = ms.PC + a
        rw [hT1pc]; bv_omega
      have haAl : holAligned 2 a = true := by
        rw [holAligned_iff]; norm_num; exact hmod
      have hal2 : holAligned 2 (ms.PC + a) = true := by
        rw [(alignedAddSub 2 ms.PC a haAl).1, halign]
      have hT2ok : arm8Ok T2 = true := by
        rw [arm8Ok_iff]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold T2; rw [if_pos hc]; show T1.PSTATE.EL = (0 : BitVec 2)
          rw [hT1el]; exact hel
        · unfold T2; rw [if_pos hc]; show T1.SCTLR_EL1.E0E = false
          rw [hT1sctlr]; exact he0
        · unfold T2; rw [if_pos hc]; show T1.SCTLR_EL1.SA0 = false
          rw [hT1sctlr]; exact hsa0
        · unfold T2; rw [if_pos hc]; show T1.TCR_EL1.TBI1 = false
          rw [hT1tcr]; exact htbi1
        · unfold T2; rw [if_pos hc]; show T1.TCR_EL1.TBI0 = false
          rw [hT1tcr]; exact htbi0
        · unfold T2; rw [if_pos hc]; show T1.exception = exception.NoException
          exact hT1exc
        · rw [hT2pc]; exact hal2
      refine ⟨hT2ok, ?_, ?_, ?_, ?_⟩
      · simp only [arm8TargetL3_getPc]
        rw [hT2pc, hs2pc, hpc]
      · intro x hx
        simp only [arm8TargetL3_getByte]
        rw [hT2mem x, hT1mem x, hs2mem x]
        exact hmem x (hs2dom ▸ hx)
      · intro k hk
        simp only [arm8TargetL3_getReg]
        rw [hT2reg, hT1reg, hs2regs k]
        exact hreg k hk
      · intro k hk
        simp [arm8ConfigL3] at hk
    · have hcs : ConditionHolds (arm8CmpCond cmp) T1 = false := Bool.eq_false_iff.mpr hc
      have hwf : wordCmpHOL cmp (Flapjack.Compiler.Encoders.AsmSem.readReg r s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg t) s1) = false := by rw [hw, hcs]
      have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
        rw [hs2, if_neg (by rw [hwf]; simp)]; simp [updPc]
      have hs2mem : ∀ x, s2.mem x = s1.mem x := by
        rw [hs2, if_neg (by rw [hwf]; simp)]; intro x; simp [updPc]
      have hs2dom : s2.memDomain = s1.memDomain := by
        rw [hs2, if_neg (by rw [hwf]; simp)]; simp [updPc]
      have hs2regs : ∀ k, s2.regs k = s1.regs k := by
        rw [hs2, if_neg (by rw [hwf]; simp)]; intro k; simp [updPc]
      have hT2pc : T2.PC = ms.PC + 8 := by
        unfold T2; rw [if_neg hc]
        show T1.PC + 4 = ms.PC + 8
        rw [hT1pc]; rw [BitVec.add_assoc]; rfl
      have h8 : holAligned 2 (ms.PC + 8) = true := by
        rw [(alignedAddSub 2 ms.PC 8 (by rw [holAligned_iff]; decide)).1, halign]
      have hT2ok : arm8Ok T2 = true := by
        rw [arm8Ok_iff]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold T2; rw [if_neg hc]; show T1.PSTATE.EL = (0 : BitVec 2)
          rw [hT1el]; exact hel
        · unfold T2; rw [if_neg hc]; show T1.SCTLR_EL1.E0E = false
          rw [hT1sctlr]; exact he0
        · unfold T2; rw [if_neg hc]; show T1.SCTLR_EL1.SA0 = false
          rw [hT1sctlr]; exact hsa0
        · unfold T2; rw [if_neg hc]; show T1.TCR_EL1.TBI1 = false
          rw [hT1tcr]; exact htbi1
        · unfold T2; rw [if_neg hc]; show T1.TCR_EL1.TBI0 = false
          rw [hT1tcr]; exact htbi0
        · unfold T2; rw [if_neg hc]; show T1.exception = exception.NoException
          exact hT1exc
        · rw [hT2pc]; exact h8
      refine ⟨hT2ok, ?_, ?_, ?_, ?_⟩
      · simp only [arm8TargetL3_getPc]
        rw [hT2pc, hs2pc, hpc]
        rfl
      · intro x hx
        simp only [arm8TargetL3_getByte]
        rw [hT2mem x, hT1mem x, hs2mem x]
        exact hmem x (hs2dom ▸ hx)
      · intro k hk
        simp only [arm8TargetL3_getReg]
        rw [hT2reg, hT1reg, hs2regs k]
        exact hreg k hk
      · intro k hk
        simp [arm8ConfigL3] at hk
  have hQ : targetStateRel arm8TargetL3 s2 (env 1 (arm8Next (env 0 (arm8Next ms)))) :=
    targetStateRel_congr (hs2dom.symm ▸ a2') hq
  have hP'1 : ∀ x, ¬ s1.memDomain x → ms.MEM x = (arm8Next ms).MEM x := by
    intro x _; rw [hn1, hT1mem]
  have hP'2 : ∀ x, ¬ s1.memDomain x →
      (env 0 (arm8Next ms)).MEM x = (arm8Next (env 0 (arm8Next ms))).MEM x := by
    intro x _; exact (hu1mem x).symm
  constructor
  · simp only [asserts, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP1, hQ⟩
  · simp only [asserts2, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP'1, hP'2, trivial⟩

/-! ## The immediate compare shapes: `LogicalImmediate@64` and
`AddSubImmediate@64` with `S := T` into `XZR` -/

/-- `Run` of the `ANDS` compare on an immediate: the `AND` result sets `N`, `Z`
and clears `C`, `V`; the `XZR` destination discards the value. -/
theorem arm8Run_logicalImmediate_ands_eq (imm : BitVec 64) (rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«LogicalImmediate@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (true, (imm, (rn, 31))))))) st =
      { st with
        PSTATE :=
          { st.PSTATE with
            N := BitVec.msb (X (TN := 64) rn st &&& imm),
            Z := (X (TN := 64) rn st &&& imm) == (0 : BitVec 64),
            C := false,
            V := false } } := by
  simp only [Run, «dfn'LogicalImmediate», SetTheFlags, «write'X», Bool.and_eq_true,
    Bool.not_true]
  rfl

/-- One `arm8Next` step on the `ANDS` immediate compare word. -/
theorem arm8Next_logicalImmediate_ands (ms : arm8_state) (imm : BitVec 64) (rn : BitVec 5)
    (N : BitVec 1) (imms immr : BitVec 6) (opc2 : BitVec 2)
    (hbm : EncodeBitMask imm = some (N, (imms, immr)))
    (hop : EncodeLogicalOp (.LogicalOp_AND, true) = some opc2)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8LogicalImmediateWord opc2 N imms immr rn 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8LogicalImmediateWord opc2 N imms immr rn 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8LogicalImmediateWord opc2 N imms immr rn 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8LogicalImmediateWord opc2 N imms immr rn 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := BitVec.msb (X (TN := 64) rn ms &&& imm),
            Z := (X (TN := 64) rn ms &&& imm) == (0 : BitVec 64),
            C := false,
            V := false } } := by
  let i : instruction := instruction.Data (Data.«LogicalImmediate@64»
    ((1 : BitVec 64), (.LogicalOp_AND, (true, (imm, (rn, 31))))))
  have hdec : Decode (arm8LogicalImmediateWord opc2 N imms immr rn 31) = i := by
    dsimp only [i]
    exact arm8Decode_logicalImmediate .LogicalOp_AND true imm rn 31 N imms immr opc2 hbm
      (by rw [hop])
  have hrun := arm8Run_logicalImmediate_ands_eq imm rn { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8LogicalImmediateWord opc2 N imms immr rn 31)
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  rfl

end Flapjack.Compiler.Encoders.Arm8.L3
