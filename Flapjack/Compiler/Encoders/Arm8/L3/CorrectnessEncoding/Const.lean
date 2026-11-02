import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediate
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 4000000

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
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
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
  have hq : targetStateRel arm8TargetL3 s2 t := by
    refine ⟨htok, ?_, ?_, ?_, ?_⟩
    · change t.PC = s2.pc
      rw [htpc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → t.MEM a = s2.mem a
      intro a ha
      rw [htmem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ j, j < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains j = false →
        t.REG (BitVec.ofNat 5 j) = s2.regs j
      intro j hj
      by_cases hjr : j = r
      · rw [hjr, htval, hs2regs r, if_pos rfl]
      · rw [htreg j hj.1 hjr, hs2regs j, if_neg hjr]
        exact hreg j hj
    · intro j hj
      simp [arm8ConfigL3] at hj
  refine ⟨0, ?_⟩
  intro env henv
  constructor
  · change targetStateRel arm8TargetL3 s2 (env 0 (arm8Next ms))
    rw [hnext]
    have hagree : Arm8L3Agree s2.memDomain (env 0 t) t := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 t
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x _ => ?_, trivial⟩
    rw [hnext]
    exact (htmem x).symm


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

end Flapjack.Compiler.Encoders.Arm8.L3
