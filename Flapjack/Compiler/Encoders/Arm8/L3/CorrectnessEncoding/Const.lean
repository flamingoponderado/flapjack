import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediate
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The L3 ARMv8 `const` encoder-correctness case

`arm8_ast` lowers a constant to one of four instruction lists:

* one zeroing `MoveWide@64 .z` when `arm8EncMovImm v` succeeds,
* one negating `MoveWide@64 .n` when `arm8EncMovImm (~~~v)` succeeds,
* one `LogicalImmediate@64 ORR false v 31 r` when `v` is an encodable bitmask,
* four `MoveWide@64 .k` instructions writing the 16-bit chunks of `v`.

This file proves the reconstruction facts (the encoder's guard says every bit
outside one 16-bit block of `v` is zero, and the returned `imm16` is exactly
that block) and the three one-instruction shapes.  The four-instruction shape
is tracked separately.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-! ## Reconstructing a word from its `arm8EncMovImm` chunk -/

/-- A word whose bits are all outside the mask `M` agrees with `w &&& M`. -/
theorem and_not_eq_zero_eq (w M : BitVec 64) (h : w &&& ~~~M = 0) : w &&& M = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  have hb := congrArg (fun x : BitVec 64 => x.getLsbD i) h
  have hz : (0 : BitVec 64).getLsbD i = false := by simp
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, hz] at hb
  cases hm : M.getLsbD i with
  | false =>
      simp only [hm, Bool.not_false, Bool.and_true] at hb
      rw [hb, Bool.false_and]
  | true =>
      simp only [hm, Bool.not_true, Bool.and_false, Bool.and_true] at hb ⊢

/-- `toNat` of a left shift of an `ofNat` word. -/
theorem toNat_ofNat_shiftLeft (imm k : Nat) :
    (BitVec.ofNat 64 imm <<< k).toNat = (imm * 2 ^ k) % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- A natural number that agrees with the mask of the `k`-th 16-bit block only
has bits inside that block: it is a multiple of `2 ^ k` whose quotient fits in
16 bits, and the quotient reproduces it. -/
theorem blockDiv (x k : Nat) (hx : x &&& ((2 ^ 16 - 1) * 2 ^ k) = x) :
    x / 2 ^ k % 2 ^ 16 = x / 2 ^ k ∧ x / 2 ^ k * 2 ^ k = x := by
  have hle : x ≤ (2 ^ 16 - 1) * 2 ^ k := by
    have h := Nat.and_le_right (n := x) (m := (2 ^ 16 - 1) * 2 ^ k)
    rwa [hx] at h
  have hlow : x &&& (2 ^ k - 1) = 0 := by
    rw [← hx, Nat.and_assoc]
    have hz : ((2 ^ 16 - 1) * 2 ^ k) &&& (2 ^ k - 1) = 0 := by
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm (2 ^ 16 - 1) (2 ^ k),
        Nat.mul_mod_right]
    rw [hz, Nat.and_zero]
  have hmod : x % 2 ^ k = 0 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod, hlow]
  have hdvd : 2 ^ k ∣ x := Nat.dvd_of_mod_eq_zero hmod
  have hdiv : x / 2 ^ k ≤ 2 ^ 16 - 1 :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hle)
  exact ⟨Nat.mod_eq_of_lt (by omega), Nat.div_mul_cancel hdvd⟩

/-- The immediate of one `arm8EncMovImm` branch reproduces the masked word. -/
theorem arm8MovWideImm_value (v : BitVec 64) (k imm16 : Nat) (hk : k ≤ 48)
    (hflag : v &&& ~~~(BitVec.ofNat 64 (0xFFFF <<< k)) = 0)
    (himm : imm16 = (v >>> k).toNat % 65536) :
    BitVec.ofNat 64 imm16 <<< k = v := by
  have hM := and_not_eq_zero_eq v (BitVec.ofNat 64 (0xFFFF <<< k)) hflag
  have hto : v.toNat &&& (BitVec.ofNat 64 (0xFFFF <<< k)).toNat = v.toNat := by
    have h := congrArg BitVec.toNat hM
    simpa using h
  have hmask : (BitVec.ofNat 64 (0xFFFF <<< k)).toNat = (2 ^ 16 - 1) * 2 ^ k := by
    rw [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hlt : 65535 * 2 ^ k < 2 ^ 64 := by
      have h2 : (2 : Nat) ^ k ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hk
      have h3 : (65535 : Nat) * 2 ^ 48 < 2 ^ 64 := by norm_num
      have := Nat.mul_le_mul_left 65535 h2
      omega
    rw [Nat.mod_eq_of_lt hlt]
    norm_num
  rw [hmask] at hto
  obtain ⟨h1, h2⟩ := blockDiv v.toNat k hto
  have hdiv : (v >>> k).toNat % 65536 = v.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact h1
  rw [himm, hdiv]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_shiftLeft, h2, Nat.mod_eq_of_lt v.isLt]

/-- `arm8EncMovImm` returns the immediate that reconstructs its argument. -/
theorem arm8EncMovImm_value (v : BitVec 64) (imm16 : BitVec 16) (hw : BitVec 2)
    (h : arm8EncMovImm v = some (imm16, hw)) :
    (BitVec.setWidth 64 imm16) <<< (hw.toNat * 16) = v := by
  unfold arm8EncMovImm at h
  split at h
  · rename_i h0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨himm, hhw⟩ := h
    rw [← himm, ← hhw, ← BitVec.ofNat_toNat]
    have hk : ((0 : BitVec 2)).toNat * 16 = 0 := by decide
    rw [hk]
    have hm : ~~~(BitVec.ofNat 64 (0xFFFF <<< 0)) = (0xFFFFFFFFFFFF0000 : BitVec 64) := by
      decide
    exact arm8MovWideImm_value v 0 (BitVec.ofNat 16 ((v >>> 0).toNat)).toNat (by decide) (by rw [hm]; exact h0) (by simp [BitVec.toNat_ofNat])
  · split at h
    · rename_i h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨himm, hhw⟩ := h
      rw [← himm, ← hhw, ← BitVec.ofNat_toNat]
      have hk : ((1 : BitVec 2)).toNat * 16 = 16 := by decide
      rw [hk]
      have hm : ~~~(BitVec.ofNat 64 (0xFFFF <<< 16)) = (0xFFFFFFFF0000FFFF : BitVec 64) := by
        decide
      exact arm8MovWideImm_value v 16 (BitVec.ofNat 16 ((v >>> 16).toNat)).toNat (by decide) (by rw [hm]; exact h1) (by simp [BitVec.toNat_ofNat])
    · split at h
      · rename_i h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨himm, hhw⟩ := h
        rw [← himm, ← hhw, ← BitVec.ofNat_toNat]
        have hk : ((2 : BitVec 2)).toNat * 16 = 32 := by decide
        rw [hk]
        have hm : ~~~(BitVec.ofNat 64 (0xFFFF <<< 32)) = (0xFFFF0000FFFFFFFF : BitVec 64) := by
          decide
        exact arm8MovWideImm_value v 32 (BitVec.ofNat 16 ((v >>> 32).toNat)).toNat (by decide) (by rw [hm]; exact h2) (by simp [BitVec.toNat_ofNat])
      · split at h
        · rename_i h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨himm, hhw⟩ := h
          rw [← himm, ← hhw, ← BitVec.ofNat_toNat]
          have hk : ((3 : BitVec 2)).toNat * 16 = 48 := by decide
          rw [hk]
          have hm : ~~~(BitVec.ofNat 64 (0xFFFF <<< 48)) = (0x0000FFFFFFFFFFFF : BitVec 64) := by
            decide
          exact arm8MovWideImm_value v 48 (BitVec.ofNat 16 ((v >>> 48).toNat)).toNat (by decide) (by rw [hm]; exact h3) (by simp [BitVec.toNat_ofNat])
        · simp at h

/-- `arm8EncMovImm` on the complement returns the immediate whose negation is
the argument, which is what the `MoveWide .n` lowering writes. -/
theorem arm8EncMovImm_value_not (v : BitVec 64) (imm16 : BitVec 16) (hw : BitVec 2)
    (h : arm8EncMovImm (~~~v) = some (imm16, hw)) :
    ~~~((BitVec.setWidth 64 imm16) <<< (hw.toNat * 16)) = v := by
  rw [arm8EncMovImm_value _ _ _ h, BitVec.not_not]


/-! ## The lowered instruction lists -/

/-- `arm8_ast` of a zeroing `MoveWide` constant. -/
theorem arm8Ast_const_movZ (r : Nat) (v : BitVec 64) (imm16 : BitVec 16) (hw : BitVec 2)
    (h : arm8EncMovImm v = some (imm16, hw)) :
    arm8Ast (.inst (.const r v)) =
      [.Data (.«MoveWide@64» (1, .z, hw, imm16, BitVec.ofNat 5 r))] := by
  simp [arm8Ast, h]

/-- `arm8_ast` of a negating `MoveWide` constant. -/
theorem arm8Ast_const_movN (r : Nat) (v : BitVec 64) (imm16 : BitVec 16) (hw : BitVec 2)
    (h0 : arm8EncMovImm v = none) (h : arm8EncMovImm (~~~v) = some (imm16, hw)) :
    arm8Ast (.inst (.const r v)) =
      [.Data (.«MoveWide@64» (1, .n, hw, imm16, BitVec.ofNat 5 r))] := by
  simp [arm8Ast, h0, h]

/-- `arm8_ast` of a bitmask `LogicalImmediate` constant. -/
theorem arm8Ast_const_orr (r : Nat) (v : BitVec 64)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (h : (EncodeBitMask v).isSome = true) :
    arm8Ast (.inst (.const r v)) =
      [.Data (.«LogicalImmediate@64» (1, .LogicalOp_ORR, false, v, 31, BitVec.ofNat 5 r))] := by
  simp [arm8Ast, h0, h1, h]

/-- `arm8_enc` of a zeroing `MoveWide` constant is the four bytes of its word. -/
theorem arm8Enc_const_movZ (r : Nat) (v : BitVec 64) (imm16 : BitVec 16) (hw : BitVec 2)
    (h : arm8EncMovImm v = some (imm16, hw)) :
    arm8Enc (.inst (.const r v)) =
      [BitVec.ofNat 8 ((arm8MoveWideWord .z hw imm16 (BitVec.ofNat 5 r) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .z hw imm16 (BitVec.ofNat 5 r) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .z hw imm16 (BitVec.ofNat 5 r) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .z hw imm16 (BitVec.ofNat 5 r) >>> 24).toNat)] := by
  rw [arm8Enc, arm8Ast_const_movZ r v imm16 hw h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [arm8Encode, arm8Encode_moveWide]

/-- `arm8_enc` of a negating `MoveWide` constant is the four bytes of its word. -/
theorem arm8Enc_const_movN (r : Nat) (v : BitVec 64) (imm16 : BitVec 16) (hw : BitVec 2)
    (h0 : arm8EncMovImm v = none) (h : arm8EncMovImm (~~~v) = some (imm16, hw)) :
    arm8Enc (.inst (.const r v)) =
      [BitVec.ofNat 8 ((arm8MoveWideWord .n hw imm16 (BitVec.ofNat 5 r) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .n hw imm16 (BitVec.ofNat 5 r) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .n hw imm16 (BitVec.ofNat 5 r) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .n hw imm16 (BitVec.ofNat 5 r) >>> 24).toNat)] := by
  rw [arm8Enc, arm8Ast_const_movN r v imm16 hw h0 h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [arm8Encode, arm8Encode_moveWide]

/-- `arm8_enc` of a bitmask `LogicalImmediate` constant is the four bytes of
its word. -/
theorem arm8Enc_const_orr (r : Nat) (v : BitVec 64) (N : BitVec 1) (imms immr : BitVec 6)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (h : (EncodeBitMask v).isSome = true)
    (hbm : EncodeBitMask v = some (N, (imms, immr))) :
    arm8Enc (.inst (.const r v)) =
      [BitVec.ofNat 8 ((arm8LogicalImmediateWord 1 N imms immr 31 (BitVec.ofNat 5 r) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8LogicalImmediateWord 1 N imms immr 31 (BitVec.ofNat 5 r) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8LogicalImmediateWord 1 N imms immr 31 (BitVec.ofNat 5 r) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8LogicalImmediateWord 1 N imms immr 31 (BitVec.ofNat 5 r) >>> 24).toNat)] := by
  rw [arm8Enc, arm8Ast_const_orr r v h0 h1 h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [arm8Encode, arm8Encode_logicalImmediate .LogicalOp_ORR false v 31 (BitVec.ofNat 5 r) N imms immr
    1 hbm (by rfl)]


/-! ## Register validity and the one-instruction shape -/

/-- `asm_reg_ok` at the L3 configuration: the destination is a real register
other than the reserved ones, and in particular not `31`. -/
theorem regOk_of_asmL3 {r : Nat} (h : asmRegOkExact r arm8ConfigL3 = true) :
    r < 32 ∧ arm8ConfigL3.avoidRegs.contains r = false ∧ r ≠ 31 := by
  simp only [asmRegOkExact, arm8ConfigL3, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hlt : r < 32 := of_decide_eq_true h1
  refine ⟨hlt, ?_, ?_⟩
  · cases hc : List.contains [18, 26, 31] r with
    | false => exact hc
    | true =>
        rw [hc] at h2
        exact Bool.noConfusion h2
  · rintro rfl
    simp at h2

/-- The result half of `AddWithCarry` for a non-inverted operand. -/
theorem arm8AddWithCarry_add (x y : BitVec 64) :
    (AddWithCarry (TN := 64) (x, (y, false))).1 = x + y := by
  simp only [AddWithCarry, Bool.false_eq_true, if_false, Nat.add_zero]
  rw [BitVec.add_def]

/-- The result half of `AddWithCarry` for an inverted operand with carry in. -/
theorem arm8AddWithCarry_sub (x y : BitVec 64) :
    (AddWithCarry (TN := 64) (x, (~~~y, true))).1 = x - y := by
  simp only [AddWithCarry, if_true]
  rw [BitVec.ofNat_add, ← BitVec.add_def, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    ← BitVec.neg_eq_not_add]

/-- `X` of a valid register number reads the register file directly. -/
theorem arm8X_of_valid (ms : arm8_state) {n : Nat} (hn : n ≠ 31) (hlt : n < 32) :
    X (TN := 64) (BitVec.ofNat 5 n) ms = ms.REG (BitVec.ofNat 5 n) := by
  have hne : BitVec.ofNat 5 n ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hn32 : n % 2 ^ 5 = n := Nat.mod_eq_of_lt (by omega)
    omega
  simp only [X, BitVec.setWidth_eq]
  split
  · exact absurd (by simpa using ‹(BitVec.ofNat 5 n == 31#5) = true›) hne
  · rfl

/-- `write'X` of a valid register number updates the register file. -/
theorem arm8WriteX_of_valid (s : arm8_state) (v : BitVec 64) {n : Nat}
    (hn : n ≠ 31) (hlt : n < 32) :
    «write'X» (TN := 64) (v, BitVec.ofNat 5 n) s =
      { s with REG := holUpdate (BitVec.ofNat 5 n) v s.REG } := by
  have hne : BitVec.ofNat 5 n ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hn32 : n % 2 ^ 5 = n := Nat.mod_eq_of_lt (by omega)
    omega
  have hcond : (!(BitVec.ofNat 5 n == 31#5)) = true := by
    cases hb : (BitVec.ofNat 5 n == 31#5)
    · rfl
    · exact absurd (by simpa using hb) hne
  simp only [«write'X», BitVec.setWidth_eq, hcond, if_true]

/-- One constructor of `encoder_correct arm8TargetL3` from a one-instruction
lowering: the single `arm8Next` step executes `i`, which writes `v` into the
destination register and changes nothing else. -/
theorem constCaseOne (r : Nat) (v : BitVec 64) (i : instruction) (t : arm8_state)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hast : arm8Ast (.inst (.const r v)) = [i])
    (hnext : arm8Next ms = t)
    (htpc : t.PC = ms.PC + 4)
    (htmem : ∀ x, t.MEM x = ms.MEM x)
    (htreg : ∀ j, j < 32 → j ≠ r → t.REG (BitVec.ofNat 5 j) = ms.REG (BitVec.ofNat 5 j))
    (htval : t.REG (BitVec.ofNat 5 r) = v)
    (htok : arm8Ok t = true)
    : CaseGoal (.inst (.const r v)) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have henclen : (arm8Enc (.inst (.const r v))).length = 4 := by
    rw [arm8Enc, hast]
    simp [arm8Encode_length]
  rw [henclen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, updPc, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, updPc, updReg]
  have hs2regs : ∀ j, s2.regs j = if j = r then v else s1.regs j := by
    intro j; rw [← hupd]; simp [asmUpd, instUpd, updPc, updReg]
  exact asmCaseOne (.const r v) r v t s1 s2 ms ⟨hs, hr⟩ hnext htpc htmem htreg htval htok
    hs2pc hs2mem hs2dom hs2regs

/-- The word emitted for a zeroing `MoveWide` constant. -/
abbrev arm8ConstMovZWord (imm16 : BitVec 16) (hw : BitVec 2) (r : Nat) : BitVec 32 :=
  arm8MoveWideWord .z hw imm16 (BitVec.ofNat 5 r)

/-- The word emitted for a negating `MoveWide` constant. -/
abbrev arm8ConstMovNWord (imm16 : BitVec 16) (hw : BitVec 2) (r : Nat) : BitVec 32 :=
  arm8MoveWideWord .n hw imm16 (BitVec.ofNat 5 r)

/-- The word emitted for a bitmask `LogicalImmediate` constant. -/
abbrev arm8ConstOrrWord (N : BitVec 1) (imms immr : BitVec 6) (r : Nat) : BitVec 32 :=
  arm8LogicalImmediateWord 1 N imms immr 31 (BitVec.ofNat 5 r)

/-! ## The zeroing `MoveWide` shape -/

/-- The `MoveWide .z` constructor of `encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_const_movZ (r : Nat) (v : BitVec 64) (imm16 : BitVec 16)
    (hw : BitVec 2) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hbm : arm8EncMovImm v = some (imm16, hw)) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
  have hregok : asmRegOkExact r arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact] using hk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asmL3 hregok
  have hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5) := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31 : BitVec 5).toNat = 31 := by decide
    rw [h31] at hto
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega : r < 32)
    omega
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.const r v))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have henc := arm8Enc_const_movZ r v imm16 hw hbm
  have hlen : (arm8Enc (.inst (.const r v))).length = 4 := by
    rw [henc]; simp
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConstMovZWord imm16 hw r >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConstMovZWord imm16 hw r >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConstMovZWord imm16 hw r >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConstMovZWord imm16 hw r >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have hdec : Decode (arm8ConstMovZWord imm16 hw r) =
      instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, BitVec.ofNat 5 r)) :=
    arm8Decode_moveWide .z hw imm16 _
  have hbr : (Run (instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, BitVec.ofNat 5 r)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_moveWide_z]
    rw [if_neg hrd]
  have hexc : (Run (instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, BitVec.ofNat 5 r)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_moveWide_z]
    rw [if_neg hrd]
    exact hexc0
  have hn := arm8Next_word ms (arm8ConstMovZWord imm16 hw r)
    (instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, BitVec.ofNat 5 r)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn]
    rw [arm8Run_moveWide_z]
    rw [if_neg hrd]
    rw [arm8EncMovImm_value v imm16 hw hbm]
    rfl
  refine constCaseOne r v
    (instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, BitVec.ofNat 5 r)))
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ ?_ hnext ?_ ?_ ?_ ?_ ?_
  · exact arm8Ast_const_movZ r v imm16 hw hbm
  · rfl
  · intro x; rfl
  · intro j hj hjne
    show (if (BitVec.ofNat 5 r) = (BitVec.ofNat 5 j) then v else ms.REG (BitVec.ofNat 5 j)) =
      ms.REG (BitVec.ofNat 5 j)
    rw [if_neg]
    intro hh
    apply hjne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega)
    have hj32 : j % 2 ^ 5 = j := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 r) = (BitVec.ofNat 5 r) then v else ms.REG (BitVec.ofNat 5 r)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4


/-! ## The negating `MoveWide` shape -/

/-- The `MoveWide .n` constructor of `encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_const_movN (r : Nat) (v : BitVec 64) (imm16 : BitVec 16)
    (hw : BitVec 2) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (h0 : arm8EncMovImm v = none) (hbm : arm8EncMovImm (~~~v) = some (imm16, hw)) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
  have hregok : asmRegOkExact r arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact] using hk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asmL3 hregok
  have hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5) := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31 : BitVec 5).toNat = 31 := by decide
    rw [h31] at hto
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega : r < 32)
    omega
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.const r v))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have henc := arm8Enc_const_movN r v imm16 hw h0 hbm
  have hlen : (arm8Enc (.inst (.const r v))).length = 4 := by
    rw [henc]; simp
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConstMovNWord imm16 hw r >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConstMovNWord imm16 hw r >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConstMovNWord imm16 hw r >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConstMovNWord imm16 hw r >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa using hh
  have hdec : Decode (arm8ConstMovNWord imm16 hw r) =
      instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, BitVec.ofNat 5 r)) :=
    arm8Decode_moveWide .n hw imm16 _
  have hbr : (Run (instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, BitVec.ofNat 5 r)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_moveWide_n]
    rw [if_neg hrd]
  have hexc : (Run (instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, BitVec.ofNat 5 r)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_moveWide_n]
    rw [if_neg hrd]
    exact hexc0
  have hn := arm8Next_word ms (arm8ConstMovNWord imm16 hw r)
    (instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, BitVec.ofNat 5 r)))
    hdec hbr hexc hb0 hb1 hb2 hb3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn]
    rw [arm8Run_moveWide_n]
    rw [if_neg hrd]
    rw [arm8EncMovImm_value_not v imm16 hw hbm]
    rfl
  refine constCaseOne r v
    (instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, BitVec.ofNat 5 r)))
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ ?_ hnext ?_ ?_ ?_ ?_ ?_
  · exact arm8Ast_const_movN r v imm16 hw h0 hbm
  · rfl
  · intro x; rfl
  · intro j hj hjne
    show (if (BitVec.ofNat 5 r) = (BitVec.ofNat 5 j) then v else ms.REG (BitVec.ofNat 5 j)) =
      ms.REG (BitVec.ofNat 5 j)
    rw [if_neg]
    intro hh
    apply hjne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega)
    have hj32 : j % 2 ^ 5 = j := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 r) = (BitVec.ofNat 5 r) then v else ms.REG (BitVec.ofNat 5 r)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4


/-! ## The bitmask `LogicalImmediate` shape -/

/-- The `LogicalImmediate ORR` constructor of `encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_const_orr (r : Nat) (v : BitVec 64) (N : BitVec 1)
    (imms immr : BitVec 6) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (hsome : (EncodeBitMask v).isSome = true)
    (hbm : EncodeBitMask v = some (N, (imms, immr))) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
  have hregok : asmRegOkExact r arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact] using hk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asmL3 hregok
  have hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5) := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31 : BitVec 5).toNat = 31 := by decide
    rw [h31] at hto
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega : r < 32)
    omega
  have hbfalse : ((BitVec.ofNat 5 r) == (31 : BitVec 5)) = false := by
    cases hb : ((BitVec.ofNat 5 r) == (31 : BitVec 5)) with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp hb) hrd
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.const r v))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have henc := arm8Enc_const_orr r v N imms immr h0 h1 hsome hbm
  have hlen : (arm8Enc (.inst (.const r v))).length = 4 := by
    rw [henc]; simp
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConstOrrWord N imms immr r >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa [arm8ConstOrrWord] using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConstOrrWord N imms immr r >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa [arm8ConstOrrWord] using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConstOrrWord N imms immr r >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa [arm8ConstOrrWord] using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConstOrrWord N imms immr r >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simpa [arm8ConstOrrWord] using hh
  have hdec : Decode (arm8ConstOrrWord N imms immr r) =
      instruction.Data (Data.«LogicalImmediate@64»
        (1, .LogicalOp_ORR, false, v, 31, BitVec.ofNat 5 r)) :=
    arm8Decode_logicalImmediate .LogicalOp_ORR false v 31 (BitVec.ofNat 5 r) N imms immr 1
      hbm (by rfl)
  have hbr : (Run (instruction.Data (Data.«LogicalImmediate@64»
      (1, .LogicalOp_ORR, false, v, 31, BitVec.ofNat 5 r)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_logicalImmediate_orr]
    simp only [hbfalse, Bool.false_eq_true, if_false]
  have hexc : (Run (instruction.Data (Data.«LogicalImmediate@64»
      (1, .LogicalOp_ORR, false, v, 31, BitVec.ofNat 5 r)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_logicalImmediate_orr]
    simp only [hbfalse, Bool.false_eq_true, if_false]
    exact hexc0
  have hn := arm8Next_word ms (arm8ConstOrrWord N imms immr r)
    (instruction.Data (Data.«LogicalImmediate@64»
      (1, .LogicalOp_ORR, false, v, 31, BitVec.ofNat 5 r)))
    hdec hbr hexc hb0 hb1 hb2 hb3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn]
    rw [arm8Run_logicalImmediate_orr]
    simp only [hbfalse, Bool.false_eq_true, if_false]
    rfl
  refine constCaseOne r v
    (instruction.Data (Data.«LogicalImmediate@64»
      (1, .LogicalOp_ORR, false, v, 31, BitVec.ofNat 5 r)))
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ ?_ hnext ?_ ?_ ?_ ?_ ?_
  · exact arm8Ast_const_orr r v h0 h1 hsome
  · rfl
  · intro x; rfl
  · intro j hj hjne
    show (if (BitVec.ofNat 5 r) = (BitVec.ofNat 5 j) then v else ms.REG (BitVec.ofNat 5 j)) =
      ms.REG (BitVec.ofNat 5 j)
    rw [if_neg]
    intro hh
    apply hjne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega)
    have hj32 : j % 2 ^ 5 = j := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 r) = (BitVec.ofNat 5 r) then v else ms.REG (BitVec.ofNat 5 r)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4


/-! ## The one-instruction constant shapes -/

/-- The three one-instruction constant lowerings of `encoder_correct
arm8TargetL3`.  The four-instruction `MoveWide .k` shape is tracked
separately. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_const_single (r : Nat) (v : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hcase : (∃ imm16 hw, arm8EncMovImm v = some (imm16, hw)) ∨
      (∃ imm16 hw, arm8EncMovImm v = none ∧ arm8EncMovImm (~~~v) = some (imm16, hw)) ∨
      (arm8EncMovImm v = none ∧ arm8EncMovImm (~~~v) = none ∧
        ∃ N imms immr, EncodeBitMask v = some (N, (imms, immr)))) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  rcases hcase with ⟨imm16, hw, hmov⟩ | ⟨imm16, hw, hnone, hmov⟩ |
    ⟨hnone, hnone2, N, imms, immr, hbm⟩
  · exact arm8_encoder_correct_const_movZ r v imm16 hw s1 s2 ms h hmov
  · exact arm8_encoder_correct_const_movN r v imm16 hw s1 s2 ms h hnone hmov
  · exact arm8_encoder_correct_const_orr r v N imms immr s1 s2 ms h hnone hnone2
      (by rw [hbm]; rfl) hbm


/-! ## The four-instruction `MoveWide .k` shape -/

/-- `arm8_ast` of the four-`MoveWide` constant. -/
theorem arm8Ast_const_movK (r : Nat) (v : BitVec 64)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (h : (EncodeBitMask v).isSome = false) :
    arm8Ast (.inst (.const r v)) =
      [.Data (.«MoveWide@64» (1, .k, 0, BitVec.ofNat 16 ((v >>> 0).toNat), BitVec.ofNat 5 r)),
       .Data (.«MoveWide@64» (1, .k, 1, BitVec.ofNat 16 ((v >>> 16).toNat), BitVec.ofNat 5 r)),
       .Data (.«MoveWide@64» (1, .k, 2, BitVec.ofNat 16 ((v >>> 32).toNat), BitVec.ofNat 5 r)),
       .Data (.«MoveWide@64» (1, .k, 3, BitVec.ofNat 16 ((v >>> 48).toNat), BitVec.ofNat 5 r))] := by
  simp [arm8Ast, h0, h1, h]

/-- Bits below sixteen are unchanged by reduction modulo `2 ^ 16`. -/
theorem testBit_mod_65536 (x i : Nat) (hi : i < 16) : (x % 65536).testBit i = x.testBit i := by
  have h : (65536 : Nat) = 2 ^ 16 := by norm_num
  rw [h, Nat.testBit_mod_two_pow]
  simp [hi]

/-- The four 16-bit insertions of the `MoveWide .k` lowering reproduce `v`. -/
theorem arm8MoveWideK_chain (x v : BitVec 64) :
    Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((v >>> 48).toNat))
      (Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((v >>> 32).toNat))
        (Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((v >>> 16).toNat))
          (Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((v >>> 0).toNat)) x))) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Flapjack.RiscV.L3.holBitFieldInsert, Flapjack.getLsbD_holFcpWord, hi,
    decide_true, Bool.true_and]
  interval_cases i <;>
    simp [BitVec.getElem_eq_testBit_toNat, testBit_mod_65536]


/-- `arm8_enc` of a `MoveWide .k` instruction is the four bytes of its word. -/
theorem arm8Encode_movK (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5) :
    arm8Encode (.Data (.«MoveWide@64» (1, .k, hw, imm16, rd))) =
      [BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_moveWide]

/-- One `arm8Next` step on a state holding the encoded `MoveWide .k` word inserts
that 16-bit chunk into the destination register. -/
theorem arm8Next_movK (ms : arm8_state) (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5)
    (hrd : rd ≠ 31) (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with branch_hint := none, REG := holUpdate rd (Flapjack.RiscV.L3.holBitFieldInsert (hw.toNat * 16 + 15) (hw.toNat * 16) imm16 (X rd ms)) ms.REG, PC := ms.PC + 4 } := by
  have hdec : Decode (arm8MoveWideWord .k hw imm16 rd) =
      instruction.Data (Data.«MoveWide@64» (1, .k, hw, imm16, rd)) :=
    arm8Decode_moveWide .k hw imm16 rd
  have hbr : (Run (instruction.Data (Data.«MoveWide@64» (1, .k, hw, imm16, rd)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_moveWide_k]
    rw [if_neg hrd]
  have hexc : (Run (instruction.Data (Data.«MoveWide@64» (1, .k, hw, imm16, rd)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_moveWide_k]
    rw [if_neg hrd]
    exact hexc0
  have hn := arm8Next_word ms (arm8MoveWideWord .k hw imm16 rd)
    (instruction.Data (Data.«MoveWide@64» (1, .k, hw, imm16, rd)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  rw [arm8Run_moveWide_k]
  rw [if_neg hrd]
  rfl


/-! ## Memory-free instructions and the run machinery -/

/-- An instruction whose `Run` does not write memory. -/
def MemFree (i : instruction) : Prop := ∀ s : arm8_state, (Run i s).MEM = s.MEM

theorem memFree_moveWide_z (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5) :
    MemFree (instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, rd))) := by
  intro s
  rw [arm8Run_moveWide_z]
  split <;> rfl

theorem memFree_moveWide_n (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5) :
    MemFree (instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, rd))) := by
  intro s
  rw [arm8Run_moveWide_n]
  split <;> rfl

theorem memFree_moveWide_k (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5) :
    MemFree (instruction.Data (Data.«MoveWide@64» (1, .k, hw, imm16, rd))) := by
  intro s
  rw [arm8Run_moveWide_k]
  split <;> rfl

/-- A two-bit word is one of its four values. -/
theorem bitvec2_cases (x : BitVec 2) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hx : x = BitVec.ofNat 2 x.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hx]
  have hlt : x.toNat < 4 := by simpa using x.isLt
  interval_cases x.toNat <;> simp

/-- `write'SP` does not write memory. -/
theorem writeSP_mem (imm : BitVec 64) (s : arm8_state) : («write'SP» imm s).MEM = s.MEM := by
  unfold «write'SP»
  by_cases hs : s.PSTATE.SPS = false
  · simp [hs]
  · have hs' : s.PSTATE.SPS = true := by cases h : s.PSTATE.SPS <;> simp_all
    simp only [hs', Bool.not_true]
    rcases bitvec2_cases s.PSTATE.EL with h | h | h | h <;> simp [h]

theorem memFree_logicalImmediate_orr (imm : BitVec 64) (rd : BitVec 5) :
    MemFree (instruction.Data (Data.«LogicalImmediate@64» (1, .LogicalOp_ORR, false, imm, 31, rd))) := by
  intro s
  rw [arm8Run_logicalImmediate_orr]
  split
  · exact writeSP_mem imm s
  · rfl


/-- `arm8_enc` of the four-`MoveWide` constant is the concatenation of the four
encoded words. -/
theorem arm8Enc_const_movK (r : Nat) (v : BitVec 64)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (h : (EncodeBitMask v).isSome = false) :
    arm8Enc (.inst (.const r v)) =
      (arm8Encode (.Data (.«MoveWide@64» (1, .k, 0, BitVec.ofNat 16 ((v >>> 0).toNat), BitVec.ofNat 5 r))) ++
       (arm8Encode (.Data (.«MoveWide@64» (1, .k, 1, BitVec.ofNat 16 ((v >>> 16).toNat), BitVec.ofNat 5 r))) ++
        (arm8Encode (.Data (.«MoveWide@64» (1, .k, 2, BitVec.ofNat 16 ((v >>> 32).toNat), BitVec.ofNat 5 r))) ++
         arm8Encode (.Data (.«MoveWide@64» (1, .k, 3, BitVec.ofNat 16 ((v >>> 48).toNat), BitVec.ofNat 5 r)))))) := by
  rw [arm8Enc, arm8Ast_const_movK r v h0 h1 h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The four-`MoveWide` constant encodes to sixteen bytes. -/
theorem arm8Enc_const_movK_length (r : Nat) (v : BitVec 64)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (h : (EncodeBitMask v).isSome = false) :
    (arm8Enc (.inst (.const r v))).length = 16 := by
  rw [arm8Enc_const_movK r v h0 h1 h]
  simp only [arm8Encode_movK, List.length_append, List.length_cons, List.length_nil]


/-- One `MoveWide .k` step preserves agreement on the source domain.  The byte
facts are stated for `t`; agreement gives them for `s`. -/
theorem arm8Next_movK_agree (d : BitVec 64 → Prop) (s t : arm8_state)
    (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5) (hrd : rd ≠ 31)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 24).toNat)) :
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
  have hd0 : d t.PC := by simpa using hf 0 (by omega)
  have hd1 : d (t.PC + 1) := by simpa using hf 1 (by omega)
  have hd2 : d (t.PC + 2) := by simpa using hf 2 (by omega)
  have hd3 : d (t.PC + 3) := by simpa using hf 3 (by omega)
  have hs0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC hd0).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) hd1).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) hd2).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) hd3).trans hb3
  have hsf : ∀ j, j < 4 → d (s.PC + BitVec.ofNat 64 j) := by
    intro j hj; rw [h.pc]; exact hf j hj
  have hss := arm8Next_movK s hw imm16 rd hrd hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_movK t hw imm16 rd hrd hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [X, h.reg]
  · simp [h.pstate]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    simp only [h.mem a ha]


/-! ## The four-instruction shape, step by step -/

/-- The four `MoveWide .k` words of the constant lowering. -/
abbrev arm8ConstMovKWord (k : Nat) (v : BitVec 64) (r : Nat) : BitVec 32 :=
  arm8MoveWideWord .k (BitVec.ofNat 2 k) (BitVec.ofNat 16 ((v >>> (k * 16)).toNat))
    (BitVec.ofNat 5 r)

/-- The four `MoveWide .k` instructions of the constant lowering. -/
abbrev arm8ConstMovKInsn (k : Nat) (v : BitVec 64) (r : Nat) : instruction :=
  .Data (.«MoveWide@64» (1, .k, BitVec.ofNat 2 k, BitVec.ofNat 16 ((v >>> (k * 16)).toNat),
    BitVec.ofNat 5 r))

/-- The state after the first `MoveWide .k` step. -/
def arm8ConstT1 (ms : arm8_state) (v : BitVec 64) (r : Nat) : arm8_state :=
  { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) (Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((v >>> 0).toNat)) (X (BitVec.ofNat 5 r) ms)) ms.REG, PC := ms.PC + 4 }

/-- The state after the second `MoveWide .k` step. -/
def arm8ConstT2 (ms : arm8_state) (v : BitVec 64) (r : Nat) : arm8_state :=
  { arm8ConstT1 ms v r with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) (Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((v >>> 16).toNat)) (X (BitVec.ofNat 5 r) (arm8ConstT1 ms v r))) (arm8ConstT1 ms v r).REG, PC := (arm8ConstT1 ms v r).PC + 4 }

/-- The state after the third `MoveWide .k` step. -/
def arm8ConstT3 (ms : arm8_state) (v : BitVec 64) (r : Nat) : arm8_state :=
  { arm8ConstT2 ms v r with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) (Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((v >>> 32).toNat)) (X (BitVec.ofNat 5 r) (arm8ConstT2 ms v r))) (arm8ConstT2 ms v r).REG, PC := (arm8ConstT2 ms v r).PC + 4 }

/-- The state after the fourth `MoveWide .k` step. -/
def arm8ConstT4 (ms : arm8_state) (v : BitVec 64) (r : Nat) : arm8_state :=
  { arm8ConstT3 ms v r with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 r) (Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((v >>> 48).toNat)) (X (BitVec.ofNat 5 r) (arm8ConstT3 ms v r))) (arm8ConstT3 ms v r).REG, PC := (arm8ConstT3 ms v r).PC + 4 }


/-- BitVec literal reassociation helpers for the four-instruction chain. -/
theorem bv_add_4_1 (a : BitVec 64) : a + 4 + 1 = a + 5 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_4_2 (a : BitVec 64) : a + 4 + 2 = a + 6 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_4_3 (a : BitVec 64) : a + 4 + 3 = a + 7 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_4_4 (a : BitVec 64) : a + 4 + 4 = a + 8 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_8_1 (a : BitVec 64) : a + 8 + 1 = a + 9 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_8_2 (a : BitVec 64) : a + 8 + 2 = a + 10 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_8_3 (a : BitVec 64) : a + 8 + 3 = a + 11 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_8_4 (a : BitVec 64) : a + 8 + 4 = a + 12 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_12_1 (a : BitVec 64) : a + 12 + 1 = a + 13 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_12_2 (a : BitVec 64) : a + 12 + 2 = a + 14 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_12_3 (a : BitVec 64) : a + 12 + 3 = a + 15 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_12_4 (a : BitVec 64) : a + 12 + 4 = a + 16 := by
  rw [BitVec.add_assoc]; congr 1

/-- `Aligned` at size four from `holAligned 2`. -/
theorem aligned_of_holAligned (pc : BitVec 64) (h : holAligned 2 pc = true) :
    Aligned (TN := 64) (pc, 4) = true := by
  rw [Aligned_four_iff]
  simpa using (holAligned_iff 2 pc).mp h

/-- The first `MoveWide .k` step reaches `arm8ConstT1`. -/
theorem arm8Next_constT1 (ms : arm8_state) (v : BitVec 64) (r : Nat)
    (hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 0).toNat))
    (hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 8).toNat))
    (hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 16).toNat))
    (hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 24).toNat)) :
    arm8Next ms = arm8ConstT1 ms v r := by
  unfold arm8ConstT1
  exact arm8Next_movK ms 0 (BitVec.ofNat 16 ((v >>> 0).toNat)) (BitVec.ofNat 5 r)
    hrd hexc0 hb0 hb1 hb2 hb3 hal he0 hel

/-- The second `MoveWide .k` step reaches `arm8ConstT2`. -/
theorem arm8Next_constT2 (ms : arm8_state) (v : BitVec 64) (r : Nat)
    (hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (hal4 : Aligned (TN := 64) (ms.PC + 4, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 0).toNat))
    (hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 8).toNat))
    (hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 16).toNat))
    (hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 24).toNat)) :
    arm8Next (arm8ConstT1 ms v r) = arm8ConstT2 ms v r := by
  unfold arm8ConstT2
  have ht1pc : (arm8ConstT1 ms v r).PC = ms.PC + 4 := rfl
  have ht1mem : ∀ a, (arm8ConstT1 ms v r).MEM a = ms.MEM a := fun _ => rfl
  refine arm8Next_movK (arm8ConstT1 ms v r) 1 (BitVec.ofNat 16 ((v >>> 16).toNat))
    (BitVec.ofNat 5 r) hrd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (arm8ConstT1 ms v r).exception = exception.NoException
    exact hexc0
  · show (arm8ConstT1 ms v r).MEM (arm8ConstT1 ms v r).PC = _
    rw [ht1pc, ht1mem]; simpa [arm8ConstMovKWord] using hb4
  · show (arm8ConstT1 ms v r).MEM ((arm8ConstT1 ms v r).PC + 1) = _
    rw [ht1pc, ht1mem, bv_add_4_1]; simpa [arm8ConstMovKWord] using hb5
  · show (arm8ConstT1 ms v r).MEM ((arm8ConstT1 ms v r).PC + 2) = _
    rw [ht1pc, ht1mem, bv_add_4_2]; simpa [arm8ConstMovKWord] using hb6
  · show (arm8ConstT1 ms v r).MEM ((arm8ConstT1 ms v r).PC + 3) = _
    rw [ht1pc, ht1mem, bv_add_4_3]; simpa [arm8ConstMovKWord] using hb7
  · show Aligned (TN := 64) ((arm8ConstT1 ms v r).PC, 4) = true
    rw [ht1pc]; exact hal4
  · show (arm8ConstT1 ms v r).SCTLR_EL1.E0E = false
    exact he0
  · show (arm8ConstT1 ms v r).PSTATE.EL = (0 : BitVec 2)
    exact hel

/-- The third `MoveWide .k` step reaches `arm8ConstT3`. -/
theorem arm8Next_constT3 (ms : arm8_state) (v : BitVec 64) (r : Nat)
    (hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (hal8 : Aligned (TN := 64) (ms.PC + 8, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb8 : ms.MEM (ms.PC + 8) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 0).toNat))
    (hb9 : ms.MEM (ms.PC + 9) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 8).toNat))
    (hb10 : ms.MEM (ms.PC + 10) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 16).toNat))
    (hb11 : ms.MEM (ms.PC + 11) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 24).toNat)) :
    arm8Next (arm8ConstT2 ms v r) = arm8ConstT3 ms v r := by
  unfold arm8ConstT3
  have ht1pc : (arm8ConstT1 ms v r).PC = ms.PC + 4 := rfl
  have ht2pc : (arm8ConstT2 ms v r).PC = ms.PC + 8 := by
    show (arm8ConstT1 ms v r).PC + 4 = ms.PC + 8
    rw [ht1pc, bv_add_4_4]
  have ht2mem : ∀ a, (arm8ConstT2 ms v r).MEM a = ms.MEM a := fun _ => rfl
  have ht2exc : (arm8ConstT2 ms v r).exception = exception.NoException := hexc0
  have ht2e0 : (arm8ConstT2 ms v r).SCTLR_EL1.E0E = false := he0
  have ht2el : (arm8ConstT2 ms v r).PSTATE.EL = (0 : BitVec 2) := hel
  refine arm8Next_movK (arm8ConstT2 ms v r) 2 (BitVec.ofNat 16 ((v >>> 32).toNat))
    (BitVec.ofNat 5 r) hrd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ht2exc
  · show (arm8ConstT2 ms v r).MEM (arm8ConstT2 ms v r).PC = _
    rw [ht2pc, ht2mem]; simpa [arm8ConstMovKWord] using hb8
  · show (arm8ConstT2 ms v r).MEM ((arm8ConstT2 ms v r).PC + 1) = _
    rw [ht2pc, ht2mem, bv_add_8_1]; simpa [arm8ConstMovKWord] using hb9
  · show (arm8ConstT2 ms v r).MEM ((arm8ConstT2 ms v r).PC + 2) = _
    rw [ht2pc, ht2mem, bv_add_8_2]; simpa [arm8ConstMovKWord] using hb10
  · show (arm8ConstT2 ms v r).MEM ((arm8ConstT2 ms v r).PC + 3) = _
    rw [ht2pc, ht2mem, bv_add_8_3]; simpa [arm8ConstMovKWord] using hb11
  · show Aligned (TN := 64) ((arm8ConstT2 ms v r).PC, 4) = true
    rw [ht2pc]; exact hal8
  · exact ht2e0
  · exact ht2el

/-- The fourth `MoveWide .k` step reaches `arm8ConstT4`. -/
theorem arm8Next_constT4 (ms : arm8_state) (v : BitVec 64) (r : Nat)
    (hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5))
    (hexc0 : ms.exception = exception.NoException)
    (hal12 : Aligned (TN := 64) (ms.PC + 12, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb12 : ms.MEM (ms.PC + 12) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 0).toNat))
    (hb13 : ms.MEM (ms.PC + 13) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 8).toNat))
    (hb14 : ms.MEM (ms.PC + 14) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 16).toNat))
    (hb15 : ms.MEM (ms.PC + 15) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 24).toNat)) :
    arm8Next (arm8ConstT3 ms v r) = arm8ConstT4 ms v r := by
  unfold arm8ConstT4
  have ht1pc : (arm8ConstT1 ms v r).PC = ms.PC + 4 := rfl
  have ht2pc : (arm8ConstT2 ms v r).PC = ms.PC + 8 := by
    show (arm8ConstT1 ms v r).PC + 4 = ms.PC + 8
    rw [ht1pc, bv_add_4_4]
  have ht3pc : (arm8ConstT3 ms v r).PC = ms.PC + 12 := by
    show (arm8ConstT2 ms v r).PC + 4 = ms.PC + 12
    rw [ht2pc, bv_add_8_4]
  have ht3mem : ∀ a, (arm8ConstT3 ms v r).MEM a = ms.MEM a := fun _ => rfl
  have ht3exc : (arm8ConstT3 ms v r).exception = exception.NoException := hexc0
  have ht3e0 : (arm8ConstT3 ms v r).SCTLR_EL1.E0E = false := he0
  have ht3el : (arm8ConstT3 ms v r).PSTATE.EL = (0 : BitVec 2) := hel
  refine arm8Next_movK (arm8ConstT3 ms v r) 3 (BitVec.ofNat 16 ((v >>> 48).toNat))
    (BitVec.ofNat 5 r) hrd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ht3exc
  · show (arm8ConstT3 ms v r).MEM (arm8ConstT3 ms v r).PC = _
    rw [ht3pc, ht3mem]; simpa [arm8ConstMovKWord] using hb12
  · show (arm8ConstT3 ms v r).MEM ((arm8ConstT3 ms v r).PC + 1) = _
    rw [ht3pc, ht3mem, bv_add_12_1]; simpa [arm8ConstMovKWord] using hb13
  · show (arm8ConstT3 ms v r).MEM ((arm8ConstT3 ms v r).PC + 2) = _
    rw [ht3pc, ht3mem, bv_add_12_2]; simpa [arm8ConstMovKWord] using hb14
  · show (arm8ConstT3 ms v r).MEM ((arm8ConstT3 ms v r).PC + 3) = _
    rw [ht3pc, ht3mem, bv_add_12_3]; simpa [arm8ConstMovKWord] using hb15
  · show Aligned (TN := 64) ((arm8ConstT3 ms v r).PC, 4) = true
    rw [ht3pc]; exact hal12
  · exact ht3e0
  · exact ht3el


/-- `holUpdate` at its own key. -/
theorem holUpdate_self {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) :
    Flapjack.RiscV.L3.holUpdate a b f a = b := by
  simp [Flapjack.RiscV.L3.holUpdate]

/-- Register value after the first `MoveWide .k` step. -/
theorem arm8ConstT1_reg (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT1 ms v r).REG (BitVec.ofNat 5 r) =
      Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((v >>> 0).toNat))
        (X (BitVec.ofNat 5 r) ms) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r)
      (Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((v >>> 0).toNat))
        (X (BitVec.ofNat 5 r) ms)) ms.REG (BitVec.ofNat 5 r) = _
  rw [holUpdate_self]

/-- Register value after the second `MoveWide .k` step. -/
theorem arm8ConstT2_reg (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT2 ms v r).REG (BitVec.ofNat 5 r) =
      Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((v >>> 16).toNat))
        (X (BitVec.ofNat 5 r) (arm8ConstT1 ms v r)) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r)
      (Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((v >>> 16).toNat))
        (X (BitVec.ofNat 5 r) (arm8ConstT1 ms v r))) (arm8ConstT1 ms v r).REG
      (BitVec.ofNat 5 r) = _
  rw [holUpdate_self]

/-- Register value after the third `MoveWide .k` step. -/
theorem arm8ConstT3_reg (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT3 ms v r).REG (BitVec.ofNat 5 r) =
      Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((v >>> 32).toNat))
        (X (BitVec.ofNat 5 r) (arm8ConstT2 ms v r)) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r)
      (Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((v >>> 32).toNat))
        (X (BitVec.ofNat 5 r) (arm8ConstT2 ms v r))) (arm8ConstT2 ms v r).REG
      (BitVec.ofNat 5 r) = _
  rw [holUpdate_self]

/-- Register value after the fourth `MoveWide .k` step. -/
theorem arm8ConstT4_reg_step (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT4 ms v r).REG (BitVec.ofNat 5 r) =
      Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((v >>> 48).toNat))
        (X (BitVec.ofNat 5 r) (arm8ConstT3 ms v r)) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r)
      (Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((v >>> 48).toNat))
        (X (BitVec.ofNat 5 r) (arm8ConstT3 ms v r))) (arm8ConstT3 ms v r).REG
      (BitVec.ofNat 5 r) = _
  rw [holUpdate_self]

/-- The four-instruction chain writes `v` into the destination register. -/
theorem arm8ConstT4_reg (ms : arm8_state) (v : BitVec 64) (r : Nat)
    (hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5)) :
    (arm8ConstT4 ms v r).REG (BitVec.ofNat 5 r) = v := by
  have hbeq : (BitVec.ofNat 5 r == BitVec.ofNat 5 31) = false := by
    rw [beq_eq_false_iff_ne]; exact hrd
  rw [arm8ConstT4_reg_step]
  simp only [X, hbeq, Bool.false_eq_true, if_false, BitVec.setWidth_eq]
  rw [arm8ConstT3_reg]
  simp only [X, hbeq, Bool.false_eq_true, if_false, BitVec.setWidth_eq]
  rw [arm8ConstT2_reg]
  simp only [X, hbeq, Bool.false_eq_true, if_false, BitVec.setWidth_eq]
  rw [arm8ConstT1_reg]
  simp only [X, hbeq, Bool.false_eq_true, if_false, BitVec.setWidth_eq]
  rw [arm8MoveWideK_chain (ms.REG (BitVec.ofNat 5 r)) v]

/-- The four-instruction chain advances the PC by sixteen. -/
theorem arm8ConstT4_pc (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT4 ms v r).PC = ms.PC + 16 := by
  have h1 : (arm8ConstT1 ms v r).PC = ms.PC + 4 := rfl
  have h2 : (arm8ConstT2 ms v r).PC = ms.PC + 8 := by
    show (arm8ConstT1 ms v r).PC + 4 = ms.PC + 8
    rw [h1, bv_add_4_4]
  have h3 : (arm8ConstT3 ms v r).PC = ms.PC + 12 := by
    show (arm8ConstT2 ms v r).PC + 4 = ms.PC + 12
    rw [h2, bv_add_8_4]
  show (arm8ConstT3 ms v r).PC + 4 = ms.PC + 16
  rw [h3, bv_add_12_4]

/-- The four-instruction chain leaves memory untouched. -/
theorem arm8ConstT4_mem (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    ∀ a, (arm8ConstT4 ms v r).MEM a = ms.MEM a := fun _ => rfl

/-- The four-instruction chain leaves the exception flag untouched. -/
theorem arm8ConstT4_exc (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT4 ms v r).exception = ms.exception := rfl

/-- The `i`-th of four consecutive words is a valid aligned code address. -/
theorem mem_allPcs_four_l3 (p : BitVec 64) (i : Nat) (hi : i < 4) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs 16 p 2 := by
  rw [allPcs_eq]
  refine ⟨i, ?_, rfl⟩
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  omega

/-- Alignment after one more four-byte word. -/
theorem holAligned_add_four (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 4) = true := by
  have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
  rw [(alignedAddSub 2 pc 4 h4).1, h]
theorem holAligned_add_eight (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 8) = true := by
  have h8 : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
  rw [(alignedAddSub 2 pc 8 h8).1, h]
theorem holAligned_add_twelve (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 12) = true := by
  have h12 : holAligned 2 (12 : BitVec 64) = true := by rw [holAligned_iff]; decide
  rw [(alignedAddSub 2 pc 12 h12).1, h]
theorem holAligned_add_sixteen (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 16) = true := by
  have h16 : holAligned 2 (16 : BitVec 64) = true := by rw [holAligned_iff]; decide
  rw [(alignedAddSub 2 pc 16 h16).1, h]

/-- Registers other than the destination are untouched by the chain. -/
theorem arm8ConstT4_reg_ne (ms : arm8_state) (v : BitVec 64) (r j : Nat)
    (hr : r < 32) (hj : j < 32) (hjr : j ≠ r) :
    (arm8ConstT4 ms v r).REG (BitVec.ofNat 5 j) = ms.REG (BitVec.ofNat 5 j) := by
  have hne : (BitVec.ofNat 5 r) ≠ (BitVec.ofNat 5 j) := by
    intro hh
    apply hjr
    have ht := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at ht
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega)
    have hj32 : j % 2 ^ 5 = j := Nat.mod_eq_of_lt (by omega)
    omega
  have h4 : (arm8ConstT4 ms v r).REG (BitVec.ofNat 5 j) =
      (arm8ConstT3 ms v r).REG (BitVec.ofNat 5 j) := by
    show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r) _ (arm8ConstT3 ms v r).REG
      (BitVec.ofNat 5 j) = _
    simp only [Flapjack.RiscV.L3.holUpdate]
    exact if_neg hne
  have h3 : (arm8ConstT3 ms v r).REG (BitVec.ofNat 5 j) =
      (arm8ConstT2 ms v r).REG (BitVec.ofNat 5 j) := by
    show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r) _ (arm8ConstT2 ms v r).REG
      (BitVec.ofNat 5 j) = _
    simp only [Flapjack.RiscV.L3.holUpdate]
    exact if_neg hne
  have h2 : (arm8ConstT2 ms v r).REG (BitVec.ofNat 5 j) =
      (arm8ConstT1 ms v r).REG (BitVec.ofNat 5 j) := by
    show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r) _ (arm8ConstT1 ms v r).REG
      (BitVec.ofNat 5 j) = _
    simp only [Flapjack.RiscV.L3.holUpdate]
    exact if_neg hne
  have h1 : (arm8ConstT1 ms v r).REG (BitVec.ofNat 5 j) =
      ms.REG (BitVec.ofNat 5 j) := by
    show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 r) _ ms.REG (BitVec.ofNat 5 j) = _
    simp only [Flapjack.RiscV.L3.holUpdate]
    exact if_neg hne
  rw [h4, h3, h2, h1]

/-- A `MoveWide .k` step leaves memory untouched (state-equation form). -/
theorem arm8Next_movK_mem (s : arm8_state) (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5)
    (hrd : rd ≠ 31) (hexc0 : s.exception = exception.NoException)
    (h0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 0).toNat))
    (h1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 8).toNat))
    (h2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 16).toNat))
    (h3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k hw imm16 rd >>> 24).toNat))
    (hal : Aligned (TN := 64) (s.PC, 4) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next s).MEM x = s.MEM x := by
  rw [arm8Next_movK s hw imm16 rd hrd hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  rfl

/-- PC after the second `MoveWide .k` step. -/
theorem arm8ConstT2_pc (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT2 ms v r).PC = ms.PC + 8 := by
  show (arm8ConstT1 ms v r).PC + 4 = ms.PC + 8
  rw [show (arm8ConstT1 ms v r).PC = ms.PC + 4 from rfl, bv_add_4_4]

/-- PC after the third `MoveWide .k` step. -/
theorem arm8ConstT3_pc (ms : arm8_state) (v : BitVec 64) (r : Nat) :
    (arm8ConstT3 ms v r).PC = ms.PC + 12 := by
  show (arm8ConstT2 ms v r).PC + 4 = ms.PC + 12
  rw [arm8ConstT2_pc ms v r, bv_add_8_4]

/-- The four-instruction `MoveWide .k` constructor of
`encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_const_movK (r : Nat) (v : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (h0 : arm8EncMovImm v = none) (h1 : arm8EncMovImm (~~~v) = none)
    (hbm : (EncodeBitMask v).isSome = false) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
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
  have hregok : asmRegOkExact r arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact] using hk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asmL3 hregok
  have hrd : (BitVec.ofNat 5 r) ≠ (31 : BitVec 5) := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31 : BitVec 5).toNat = 31 := by decide
    rw [h31] at hto
    have hr32 : r % 2 ^ 5 = r := Nat.mod_eq_of_lt (by omega : r < 32)
    omega
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := aligned_of_holAligned ms.PC halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.const r v))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have henc := arm8Enc_const_movK r v h0 h1 hbm
  have henclen : (arm8Enc (.inst (.const r v))).length = 16 := arm8Enc_const_movK_length r v h0 h1 hbm
  have henc' : arm8Enc (.inst (.const r v)) =
      (arm8Encode (.Data (.«MoveWide@64» (1, .k, 0, BitVec.ofNat 16 ((v >>> 0).toNat), BitVec.ofNat 5 r))) ++
        (arm8Encode (.Data (.«MoveWide@64» (1, .k, 1, BitVec.ofNat 16 ((v >>> 16).toNat), BitVec.ofNat 5 r))) ++
          (arm8Encode (.Data (.«MoveWide@64» (1, .k, 2, BitVec.ofNat 16 ((v >>> 32).toNat), BitVec.ofNat 5 r))) ++
            arm8Encode (.Data (.«MoveWide@64» (1, .k, 3, BitVec.ofNat 16 ((v >>> 48).toNat), BitVec.ofNat 5 r)))))) := henc
  rw [arm8Encode_movK, arm8Encode_movK, arm8Encode_movK, arm8Encode_movK] at henc'
  have hbyte (i : Nat) (hi : i < 16) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) = (arm8Enc (.inst (.const r v))).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [henclen]; exact hi)
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8ConstMovKWord 0 v r >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 0).toNat) := by
    have hh := hbyte 4 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 8).toNat) := by
    have hh := hbyte 5 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 16).toNat) := by
    have hh := hbyte 6 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((arm8ConstMovKWord 1 v r >>> 24).toNat) := by
    have hh := hbyte 7 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb8 : ms.MEM (ms.PC + 8) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 0).toNat) := by
    have hh := hbyte 8 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb9 : ms.MEM (ms.PC + 9) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 8).toNat) := by
    have hh := hbyte 9 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb10 : ms.MEM (ms.PC + 10) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 16).toNat) := by
    have hh := hbyte 10 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb11 : ms.MEM (ms.PC + 11) = BitVec.ofNat 8 ((arm8ConstMovKWord 2 v r >>> 24).toNat) := by
    have hh := hbyte 11 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb12 : ms.MEM (ms.PC + 12) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 0).toNat) := by
    have hh := hbyte 12 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb13 : ms.MEM (ms.PC + 13) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 8).toNat) := by
    have hh := hbyte 13 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb14 : ms.MEM (ms.PC + 14) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 16).toNat) := by
    have hh := hbyte 14 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hb15 : ms.MEM (ms.PC + 15) = BitVec.ofNat 8 ((arm8ConstMovKWord 3 v r >>> 24).toNat) := by
    have hh := hbyte 15 (by norm_num)
    rw [henc'] at hh
    simpa [arm8ConstMovKWord] using hh
  have hal4 : holAligned 2 (ms.PC + 4) = true := holAligned_add_four ms.PC halign
  have hal8 : holAligned 2 (ms.PC + 8) = true := holAligned_add_eight ms.PC halign
  have hal12 : holAligned 2 (ms.PC + 12) = true := holAligned_add_twelve ms.PC halign
  have hal16 : holAligned 2 (ms.PC + 16) = true := holAligned_add_sixteen ms.PC halign
  have hal4a : Aligned (TN := 64) (ms.PC + 4, 4) = true := aligned_of_holAligned _ hal4
  have hal8a : Aligned (TN := 64) (ms.PC + 8, 4) = true := aligned_of_holAligned _ hal8
  have hal12a : Aligned (TN := 64) (ms.PC + 12, 4) = true := aligned_of_holAligned _ hal12
  have hnext1 : arm8Next ms = arm8ConstT1 ms v r :=
    arm8Next_constT1 ms v r hrd hexc0 hal he0 hel hb0 hb1 hb2 hb3
  have hnext2 : arm8Next (arm8ConstT1 ms v r) = arm8ConstT2 ms v r :=
    arm8Next_constT2 ms v r hrd hexc0 hal4a he0 hel hb4 hb5 hb6 hb7
  have hnext3 : arm8Next (arm8ConstT2 ms v r) = arm8ConstT3 ms v r :=
    arm8Next_constT3 ms v r hrd hexc0 hal8a he0 hel hb8 hb9 hb10 hb11
  have hnext4 : arm8Next (arm8ConstT3 ms v r) = arm8ConstT4 ms v r :=
    arm8Next_constT4 ms v r hrd hexc0 hal12a he0 hel hb12 hb13 hb14 hb15
  have hok1 : arm8Ok (arm8ConstT1 ms v r) = true := by
    rw [arm8Ok_iff]; exact ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, hal4⟩
  have hok2 : arm8Ok (arm8ConstT2 ms v r) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8ConstT2_pc]; exact hal8
  have hok3 : arm8Ok (arm8ConstT3 ms v r) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8ConstT3_pc]; exact hal12
  have hok4 : arm8Ok (arm8ConstT4 ms v r) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8ConstT4_pc]; exact hal16
  have ht4pc : (arm8ConstT4 ms v r).PC = ms.PC + 16 := arm8ConstT4_pc ms v r
  have ht4mem : ∀ x, (arm8ConstT4 ms v r).MEM x = ms.MEM x := arm8ConstT4_mem ms v r
  have ht4reg : (arm8ConstT4 ms v r).REG (BitVec.ofNat 5 r) = v := arm8ConstT4_reg ms v r hrd
  -- byte facts at the intermediate states
  have ht1b0 : (arm8ConstT1 ms v r).MEM (arm8ConstT1 ms v r).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 0).toNat) := hb4
  have ht1b1 : (arm8ConstT1 ms v r).MEM ((arm8ConstT1 ms v r).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 8).toNat) := by
    rw [show (arm8ConstT1 ms v r).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_1]
    exact hb5
  have ht1b2 : (arm8ConstT1 ms v r).MEM ((arm8ConstT1 ms v r).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 16).toNat) := by
    rw [show (arm8ConstT1 ms v r).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_2]
    exact hb6
  have ht1b3 : (arm8ConstT1 ms v r).MEM ((arm8ConstT1 ms v r).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 24).toNat) := by
    rw [show (arm8ConstT1 ms v r).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_3]
    exact hb7
  have ht2b0 : (arm8ConstT2 ms v r).MEM (arm8ConstT2 ms v r).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 0).toNat) := by
    rw [arm8ConstT2_pc]
    exact hb8
  have ht2b1 : (arm8ConstT2 ms v r).MEM ((arm8ConstT2 ms v r).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 8).toNat) := by
    rw [arm8ConstT2_pc, bv_add_8_1]
    exact hb9
  have ht2b2 : (arm8ConstT2 ms v r).MEM ((arm8ConstT2 ms v r).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 16).toNat) := by
    rw [arm8ConstT2_pc, bv_add_8_2]
    exact hb10
  have ht2b3 : (arm8ConstT2 ms v r).MEM ((arm8ConstT2 ms v r).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 24).toNat) := by
    rw [arm8ConstT2_pc, bv_add_8_3]
    exact hb11
  have ht3b0 : (arm8ConstT3 ms v r).MEM (arm8ConstT3 ms v r).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 0).toNat) := by
    rw [arm8ConstT3_pc]
    exact hb12
  have ht3b1 : (arm8ConstT3 ms v r).MEM ((arm8ConstT3 ms v r).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 8).toNat) := by
    rw [arm8ConstT3_pc, bv_add_12_1]
    exact hb13
  have ht3b2 : (arm8ConstT3 ms v r).MEM ((arm8ConstT3 ms v r).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 16).toNat) := by
    rw [arm8ConstT3_pc, bv_add_12_2]
    exact hb14
  have ht3b3 : (arm8ConstT3 ms v r).MEM ((arm8ConstT3 ms v r).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 24).toNat) := by
    rw [arm8ConstT3_pc, bv_add_12_3]
    exact hb15
  -- instruction bytes lie in the source domain
  have hdom1 : ∀ j, j < 4 → s1.memDomain ((arm8ConstT1 ms v r).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8ConstT1 ms v r).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (4 + j) := by
      show ms.PC + (4 : BitVec 64) + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j)
      rw [hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom (4 + j) (by omega)
  have hdom2 : ∀ j, j < 4 → s1.memDomain ((arm8ConstT2 ms v r).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8ConstT2 ms v r).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (8 + j) := by
      rw [arm8ConstT2_pc, hpc]
      exact bv_add_split s1.pc 8 j
    rw [h1]
    exact hdom (8 + j) (by omega)
  have hdom3 : ∀ j, j < 4 → s1.memDomain ((arm8ConstT3 ms v r).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8ConstT3 ms v r).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (12 + j) := by
      rw [arm8ConstT3_pc, hpc]
      exact bv_add_split s1.pc 12 j
    rw [h1]
    exact hdom (12 + j) (by omega)
  -- the assembler update
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [henclen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 16 := by rw [← hupd]; simp [asmUpd, instUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by intro x; rw [← hupd]; simp [asmUpd, instUpd, updPc, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [← hupd]; simp [asmUpd, instUpd, updPc, updReg]
  have hs2regs : ∀ j, s2.regs j = if j = r then v else s1.regs j := by
    intro j; rw [← hupd]; simp [asmUpd, instUpd, updPc, updReg]
  have hq : targetStateRel arm8TargetL3 s2 (arm8ConstT4 ms v r) := by
    refine ⟨hok4, ?_, ?_, ?_, ?_⟩
    · change (arm8ConstT4 ms v r).PC = s2.pc
      rw [ht4pc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → (arm8ConstT4 ms v r).MEM a = s2.mem a
      intro a ha
      rw [ht4mem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ j, j < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains j = false →
        (arm8ConstT4 ms v r).REG (BitVec.ofNat 5 j) = s2.regs j
      intro j hj
      by_cases hjr : j = r
      · rw [hjr, ht4reg, hs2regs r, if_pos rfl]
      · rw [arm8ConstT4_reg_ne ms v r j (by omega) (by simpa [arm8ConfigL3] using hj.1) hjr,
          hs2regs j, if_neg hjr]
        exact hreg j hj
    · intro j hj
      simp [arm8ConfigL3] at hj
  refine ⟨3, ?_⟩
  intro env henv
  dsimp only
  simp only [arm8ConfigL3, henclen]
  have hcode : allPcs 16 s1.pc 0 ⊆ s1.memDomain := by
    have h0' := bytesInMemory_allPcs (arm8Enc (.inst (.const r v))) s1.pc s1.mem s1.memDomain 0 hb
    rw [henclen] at h0'
    exact h0'
  have hagree : ∀ k x, Arm8L3Agree s1.memDomain (env k x) x :=
    fun k x => (arm8Proj_eq_iff s1.memDomain _ _).mp (henv k x)
  have a1 : Arm8L3Agree s1.memDomain (env 0 (arm8Next ms)) (arm8ConstT1 ms v r) := by
    rw [hnext1]
    exact hagree 0 _
  have a2 : Arm8L3Agree s1.memDomain (arm8Next (env 0 (arm8Next ms))) (arm8ConstT2 ms v r) := by
    have hh := arm8Next_movK_agree s1.memDomain (env 0 (arm8Next ms)) (arm8ConstT1 ms v r) a1
      (by rw [arm8Ok_congr a1]; exact hok1) (1 : BitVec 2)
      (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) hrd
      hdom1 ht1b0 ht1b1 ht1b2 ht1b3
    rw [hnext2] at hh
    exact hh
  have a2' : Arm8L3Agree s1.memDomain (env 1 (arm8Next (env 0 (arm8Next ms)))) (arm8ConstT2 ms v r) :=
    (hagree 1 (arm8Next (env 0 (arm8Next ms)))).trans a2
  have a3 : Arm8L3Agree s1.memDomain (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms))))) (arm8ConstT3 ms v r) := by
    have hh := arm8Next_movK_agree s1.memDomain (env 1 (arm8Next (env 0 (arm8Next ms)))) (arm8ConstT2 ms v r) a2'
      (by rw [arm8Ok_congr a2']; exact hok2) (2 : BitVec 2)
      (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) hrd
      hdom2 ht2b0 ht2b1 ht2b2 ht2b3
    rw [hnext3] at hh
    exact hh
  have a3' : Arm8L3Agree s1.memDomain (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))) (arm8ConstT3 ms v r) :=
    (hagree 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).trans a3
  have a4 : Arm8L3Agree s1.memDomain (arm8Next (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms))))))) (arm8ConstT4 ms v r) := by
    have hh := arm8Next_movK_agree s1.memDomain (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))) (arm8ConstT3 ms v r) a3'
      (by rw [arm8Ok_congr a3']; exact hok3) (3 : BitVec 2)
      (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) hrd
      hdom3 ht3b0 ht3b1 ht3b2 ht3b3
    rw [hnext4] at hh
    exact hh
  have a4' : Arm8L3Agree s1.memDomain (env 3 (arm8Next (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))))) (arm8ConstT4 ms v r) :=
    (hagree 3 (arm8Next (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))))).trans a4
  have hu1b0 : (env 0 (arm8Next ms)).MEM (env 0 (arm8Next ms)).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 0).toNat) := by
    rw [a1.pc]
    exact (a1.mem _ (by simpa using hdom1 0)).trans ht1b0
  have hu1b1 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 8).toNat) := by
    rw [a1.pc]
    exact (a1.mem _ (by simpa using hdom1 1)).trans ht1b1
  have hu1b2 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 16).toNat) := by
    rw [a1.pc]
    exact (a1.mem _ (by simpa using hdom1 2)).trans ht1b2
  have hu1b3 : (env 0 (arm8Next ms)).MEM ((env 0 (arm8Next ms)).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) >>> 24).toNat) := by
    rw [a1.pc]
    exact (a1.mem _ (by simpa using hdom1 3)).trans ht1b3
  have hu2b0 : (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM (env 1 (arm8Next (env 0 (arm8Next ms)))).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 0).toNat) := by
    rw [a2'.pc]
    exact (a2'.mem _ (by simpa using hdom2 0)).trans ht2b0
  have hu2b1 : (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM ((env 1 (arm8Next (env 0 (arm8Next ms)))).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 8).toNat) := by
    rw [a2'.pc]
    exact (a2'.mem _ (by simpa using hdom2 1)).trans ht2b1
  have hu2b2 : (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM ((env 1 (arm8Next (env 0 (arm8Next ms)))).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 16).toNat) := by
    rw [a2'.pc]
    exact (a2'.mem _ (by simpa using hdom2 2)).trans ht2b2
  have hu2b3 : (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM ((env 1 (arm8Next (env 0 (arm8Next ms)))).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) >>> 24).toNat) := by
    rw [a2'.pc]
    exact (a2'.mem _ (by simpa using hdom2 3)).trans ht2b3
  have hu3b0 : (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 0).toNat) := by
    rw [a3'.pc]
    exact (a3'.mem _ (by simpa using hdom3 0)).trans ht3b0
  have hu3b1 : (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM ((env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 8).toNat) := by
    rw [a3'.pc]
    exact (a3'.mem _ (by simpa using hdom3 1)).trans ht3b1
  have hu3b2 : (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM ((env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 16).toNat) := by
    rw [a3'.pc]
    exact (a3'.mem _ (by simpa using hdom3 2)).trans ht3b2
  have hu3b3 : (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM ((env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) >>> 24).toNat) := by
    rw [a3'.pc]
    exact (a3'.mem _ (by simpa using hdom3 3)).trans ht3b3
  have hu1mem : ∀ x, (arm8Next (env 0 (arm8Next ms))).MEM x = (env 0 (arm8Next ms)).MEM x :=
    arm8Next_movK_mem (env 0 (arm8Next ms)) (1 : BitVec 2) (BitVec.ofNat 16 ((v >>> 16).toNat)) (BitVec.ofNat 5 r) hrd
      (a1.exc.trans hexc0) hu1b0 hu1b1 hu1b2 hu1b3
      (by rw [a1.pc]; exact hal4a)
      (by rw [a1.sctlr]; exact he0)
      (by rw [a1.pstate]; exact hel)
  have hu2mem : ∀ x, (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms))))).MEM x = (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM x :=
    arm8Next_movK_mem (env 1 (arm8Next (env 0 (arm8Next ms)))) (2 : BitVec 2) (BitVec.ofNat 16 ((v >>> 32).toNat)) (BitVec.ofNat 5 r) hrd
      (a2'.exc.trans hexc0) hu2b0 hu2b1 hu2b2 hu2b3
      (by rw [a2'.pc, arm8ConstT2_pc]; exact hal8a)
      (by rw [a2'.sctlr]; exact he0)
      (by rw [a2'.pstate]; exact hel)
  have hu3mem : ∀ x, (arm8Next (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms))))))).MEM x = (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM x :=
    arm8Next_movK_mem (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))) (3 : BitVec 2) (BitVec.ofNat 16 ((v >>> 48).toNat)) (BitVec.ofNat 5 r) hrd
      (a3'.exc.trans hexc0) hu3b0 hu3b1 hu3b2 hu3b3
      (by rw [a3'.pc, arm8ConstT3_pc]; exact hal12a)
      (by rw [a3'.sctlr]; exact he0)
      (by rw [a3'.pstate]; exact hel)
  have hP1 : arm8Ok (env 0 (arm8Next ms)) = true ∧
      (∀ pc, pc ∈ allPcs 16 s1.pc 0 → (env 0 (arm8Next ms)).MEM pc = ms.MEM pc) ∧
      (env 0 (arm8Next ms)).PC ∈ allPcs 16 s1.pc 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [arm8Ok_congr a1]; exact hok1
    · intro pc hpc'
      simpa [arm8ConstT1] using (a1.mem pc (hcode hpc'))
    · rw [a1.pc]
      rw [show (arm8ConstT1 ms v r).PC = ms.PC + (4 : BitVec 64) from by
        rfl, hpc]
      simpa using mem_allPcs_four_l3 s1.pc 1 (by norm_num)
  have hP2 : arm8Ok (env 1 (arm8Next (env 0 (arm8Next ms)))) = true ∧
      (∀ pc, pc ∈ allPcs 16 s1.pc 0 → (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM pc = ms.MEM pc) ∧
      (env 1 (arm8Next (env 0 (arm8Next ms)))).PC ∈ allPcs 16 s1.pc 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [arm8Ok_congr a2']; exact hok2
    · intro pc hpc'
      simpa [arm8ConstT1, arm8ConstT2] using (a2'.mem pc (hcode hpc'))
    · rw [a2'.pc]
      rw [show (arm8ConstT2 ms v r).PC = ms.PC + (8 : BitVec 64) from by
        rw [arm8ConstT2_pc], hpc]
      simpa using mem_allPcs_four_l3 s1.pc 2 (by norm_num)
  have hP3 : arm8Ok (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))) = true ∧
      (∀ pc, pc ∈ allPcs 16 s1.pc 0 → (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM pc = ms.MEM pc) ∧
      (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).PC ∈ allPcs 16 s1.pc 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [arm8Ok_congr a3']; exact hok3
    · intro pc hpc'
      simpa [arm8ConstT1, arm8ConstT2, arm8ConstT3] using (a3'.mem pc (hcode hpc'))
    · rw [a3'.pc]
      rw [show (arm8ConstT3 ms v r).PC = ms.PC + (12 : BitVec 64) from by
        rw [arm8ConstT3_pc], hpc]
      simpa using mem_allPcs_four_l3 s1.pc 3 (by norm_num)
  have hQ : targetStateRel arm8TargetL3 s2 (env 3 (arm8Next (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))))) :=
    targetStateRel_congr (hs2dom.symm ▸ a4') hq
  have hP'1 : ∀ x, ¬ s1.memDomain x → ms.MEM x = (arm8Next ms).MEM x := by
    intro x _
    rw [hnext1]
    rfl
  have hP'2 : ∀ x, ¬ s1.memDomain x → (env 0 (arm8Next ms)).MEM x = (arm8Next (env 0 (arm8Next ms))).MEM x := by
    intro x _
    exact (hu1mem x).symm
  have hP'3 : ∀ x, ¬ s1.memDomain x → (env 1 (arm8Next (env 0 (arm8Next ms)))).MEM x = (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms))))).MEM x := by
    intro x _
    exact (hu2mem x).symm
  have hP'4 : ∀ x, ¬ s1.memDomain x → (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms)))))).MEM x = (arm8Next (env 2 (arm8Next (env 1 (arm8Next (env 0 (arm8Next ms))))))).MEM x := by
    intro x _
    exact (hu3mem x).symm
  constructor
  · simp only [asserts, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP1, hP2, hP3, hQ⟩
  · simp only [asserts2, Nat.reduceAdd, Nat.reduceSub]
    exact ⟨hP'1, hP'2, hP'3, hP'4, trivial⟩

/-- The `const` constructor of `encoder_correct arm8TargetL3`, by the four
shapes of `arm8_ast`: zeroing, negating and bitmask `MoveWide`, then the
four-instruction `MoveWide .k` lowering. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_const (r : Nat) (v : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.const r v)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  cases hz : arm8EncMovImm v with
  | some p =>
    obtain ⟨imm16, hw⟩ := p
    exact arm8_encoder_correct_const_movZ r v imm16 hw s1 s2 ms h hz
  | none =>
    cases hn : arm8EncMovImm (~~~v) with
    | some p =>
      obtain ⟨imm16, hw⟩ := p
      exact arm8_encoder_correct_const_movN r v imm16 hw s1 s2 ms h hz hn
    | none =>
      cases hb : EncodeBitMask v with
      | some p =>
        obtain ⟨N, imms, immr⟩ := p
        exact arm8_encoder_correct_const_orr r v N imms immr s1 s2 ms h hz hn
          (by rw [hb]; rfl) hb
      | none =>
        exact arm8_encoder_correct_const_movK r v s1 s2 ms h hz hn (by rw [hb]; rfl)

end Flapjack.Compiler.Encoders.Arm8.L3

