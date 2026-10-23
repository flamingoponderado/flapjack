/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.JumpCmpCase
import Flapjack.Compiler.Encoders.Arm8.Machine.MaskConverses

/-!
# The ARM8 `const` encoder-correctness case

This file proves the `.const r v` case of `encoder_correct arm8Target`, the ARM8
analogue of `case_const` in `Flapjack/Mips32/TargetProof/Arith.lean`.  A constant
is a plain source instruction, so the case is stated at
`HolAsm.inst (HolInst.const r v)`, i.e. `.inst (.const r v)`: `HolAsm` itself has
no `const` constructor and `arm8_ast` matches the `.inst` clause first.

`arm8_ast` lowers a constant to one of four instruction lists
(`Machine/Target.lean`):

* one zeroing `moveWide .z hw imm16 r` when `enc_mov_imm v = some (imm16, hw)`,
* one negating `moveWide .n hw imm16 r` when `enc_mov_imm (~~~v)` succeeds,
* one `logicalImmediate .orr false v 31 r` when `v` is an encodable bitmask, and
* four `moveWide .k` instructions writing the 16-bit chunks of `v` in turn.

Each shape is one interference-free `arm8Next` run whose last state holds `v` in
`r`: one step in the first three shapes (`n = 0`) and four steps in the last
(`n = 3`).  The first three only have to identify the value a single instruction
writes; the fourth inserts the four chunks one at a time and reproduces `v` by
`locTemp_chain` from `Machine/ControlCase.lean`, exactly as the long `loc` form
does.

The reconstruction facts `encMovImm_some_val`/`encMovImm_some_val_not` are where
the encoder meets the decoder of the value: the guard of each `enc_mov_imm`
branch says that every bit outside one 16-bit chunk of `v` is zero, and the
returned `imm16` is exactly that chunk (`movWideImm_value`, `blockDiv`).

Like the other cases in `Machine/ControlCase.lean`, this is a case split of the
single HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`Inst`/`Const` branch has no per-case declaration of its own; the module is
Flapjack infrastructure and carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Reconstructing a word from its `enc_mov_imm` chunk -/

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

/-- A natural number that agrees with the mask of the `k`-th 16-bit block only has
bits inside that block: it is a multiple of `2 ^ k` whose quotient fits in 16
bits, and the quotient reproduces it. -/
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

/-- The immediate of one `enc_mov_imm` branch reproduces the masked word: if every
bit of `v` outside the 16-bit block at position `k` is zero and `imm16` is the
block's value, then `imm16 <<< k` is `v`. -/
theorem movWideImm_value (v : BitVec 64) (k imm16 : Nat) (hk : k ≤ 48)
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

/-- `enc_mov_imm` returns the immediate that reconstructs its argument. -/
theorem encMovImm_some_val (v : BitVec 64) (imm16 hw : Nat)
    (h : encMovImm v = some (imm16, hw)) :
    BitVec.ofNat 64 imm16 <<< (hw * 16) = v := by
  unfold encMovImm at h
  by_cases h0 : v &&& ~~~(0xFFFF : W) = 0
  · rw [ite_eq_left h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact movWideImm_value v 0 _ (by decide) (by simpa using h0) (by simp)
  · rw [ite_eq_right h0] at h
    by_cases h1 : v &&& ~~~(0xFFFF0000 : W) = 0
    · rw [ite_eq_left h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact movWideImm_value v 16 _ (by decide) (by simpa using h1) (by simp)
    · rw [ite_eq_right h1] at h
      by_cases h2 : v &&& ~~~(0xFFFF00000000 : W) = 0
      · rw [ite_eq_left h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact movWideImm_value v 32 _ (by decide) (by simpa using h2) (by simp)
      · rw [ite_eq_right h2] at h
        by_cases h3 : v &&& ~~~(0xFFFF000000000000 : W) = 0
        · rw [ite_eq_left h3] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact movWideImm_value v 48 _ (by decide) (by simpa using h3) (by simp)
        · rw [ite_eq_right h3] at h
          exact absurd h (by simp)

/-- `enc_mov_imm` on the complement returns the immediate whose negation is the
argument, which is what the `moveWide .n` lowering writes. -/
theorem encMovImm_some_val_not (v : BitVec 64) (imm16 hw : Nat)
    (h : encMovImm (~~~v) = some (imm16, hw)) :
    ~~~(BitVec.ofNat 64 imm16 <<< (hw * 16)) = v := by
  rw [encMovImm_some_val _ _ _ h, BitVec.not_not]

/-- The `hw` and `imm16` returned by `enc_mov_imm` fit the `moveWide` encoding. -/
theorem encMovImm_some_lt (v : BitVec 64) (imm16 hw : Nat)
    (h : encMovImm v = some (imm16, hw)) : hw < 4 ∧ imm16 < 65536 := by
  unfold encMovImm at h
  by_cases h0 : v &&& ~~~(0xFFFF : W) = 0
  · rw [ite_eq_left h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by decide, Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)⟩
  · rw [ite_eq_right h0] at h
    by_cases h1 : v &&& ~~~(0xFFFF0000 : W) = 0
    · rw [ite_eq_left h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)⟩
    · rw [ite_eq_right h1] at h
      by_cases h2 : v &&& ~~~(0xFFFF00000000 : W) = 0
      · rw [ite_eq_left h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by decide, Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)⟩
      · rw [ite_eq_right h2] at h
        by_cases h3 : v &&& ~~~(0xFFFF000000000000 : W) = 0
        · rw [ite_eq_left h3] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by decide, Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)⟩
        · rw [ite_eq_right h3] at h
          exact absurd h (by simp)

/-! ## The lowered instruction lists -/

/-- `arm8_ast` of a zeroing `moveWide` constant. -/
theorem arm8Ast_const_movZ (r : Nat) (v : BitVec 64) (imm16 hw : Nat)
    (h : encMovImm v = some (imm16, hw)) :
    arm8Ast (.inst (.const r v)) = [.moveWide .z hw imm16 r] := by
  simp [arm8Ast, arm8Inst, h]

/-- `arm8_ast` of a negating `moveWide` constant. -/
theorem arm8Ast_const_movN (r : Nat) (v : BitVec 64) (imm16 hw : Nat)
    (h0 : encMovImm v = none) (h : encMovImm (~~~v) = some (imm16, hw)) :
    arm8Ast (.inst (.const r v)) = [.moveWide .n hw imm16 r] := by
  simp [arm8Ast, arm8Inst, h0, h]

/-- `arm8_ast` of a bitmask `logicalImmediate` constant. -/
theorem arm8Ast_const_orr (r : Nat) (v : BitVec 64)
    (h0 : encMovImm v = none) (h1 : encMovImm (~~~v) = none)
    (h : (encodeBitMask v).isSome = true) :
    arm8Ast (.inst (.const r v)) = [.logicalImmediate .orr false v 31 r] := by
  simp [arm8Ast, arm8Inst, h0, h1, h]

/-- `arm8_ast` of the four-`moveWide` constant. -/
theorem arm8Ast_const_movK (r : Nat) (v : BitVec 64)
    (h0 : encMovImm v = none) (h1 : encMovImm (~~~v) = none)
    (h : (encodeBitMask v).isSome = false) :
    arm8Ast (.inst (.const r v)) =
      [.moveWide .k 0 (v.toNat % 65536) r,
       .moveWide .k 1 ((v >>> 16).toNat % 65536) r,
       .moveWide .k 2 ((v >>> 32).toNat % 65536) r,
       .moveWide .k 3 ((v >>> 48).toNat % 65536) r] := by
  simp [arm8Ast, arm8Inst, h0, h1, h]

/-! ## The `n = 0` shapes -/

/-- One constructor of `encoder_correct arm8Target` from a one-instruction
lowering: the single `arm8Next` step executes `i`, which writes `v` into the
destination register and changes nothing else. -/
theorem constCaseOne (r : Nat) (v : BitVec 64) (i : Insn) (t : Arm8State)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.const r v)) s2 ∧ targetStateRel arm8Target s1 ms)
    (hast : arm8Ast (.inst (.const r v)) = [i])
    (hnext : arm8Next ms = t)
    (htpc : t.pc = ms.pc + 4)
    (htmem : ∀ x, t.mem x = ms.mem x)
    (htreg : ∀ j, j ≠ r → t.regs j = ms.regs j)
    (htval : t.regs r = v)
    (htfailed : t.failed = ms.failed)
    (htal : holAligned 2 t.pc = true)
    (hsafe0 : StepSafe s1.memDomain ms) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  have st := arm8Start (.inst (.const r v)) s1 s2 ms h
  have hok : asmRegOkExact r arm8Config = true := by
    simpa only [asmOkExact, asmInstOkExact] using st.asmOk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm hok
  have hlen : (arm8Enc (.inst (.const r v))).length = 4 := by
    rw [arm8Enc, hast, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_length]
  have hupd : asmUpd (.inst (.const r v)) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 4 := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j = (if j = r then v else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc, updReg]
  have hcode : allPcs (arm8Target.config.encode (.inst (.const r v))).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq1 : arm8Target.stateOk t = true :=
    arm8StateOk_set t htal (htfailed.trans st.msFailed)
  have hq2 : t.pc = s2.pc := by
    rw [htpc, st.pc, hs2pc]
  have hq3 : ∀ x, s2.memDomain x → t.mem x = s2.mem x := by
    intro x hx
    rw [htmem x, hs2mem x]
    exact st.mem x (hs2dom ▸ hx)
  have hq4 : ∀ j, j < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains j = false → t.regs j = s2.regs j := by
    intro j hj
    by_cases hjr : j = r
    · rw [hjr, htval, hs2regs r, ite_eq_left rfl]
    · rw [htreg j hjr, hs2regs j, ite_eq_right hjr]
      exact st.reg j hj
  have hq5 : ∀ j, j < arm8Target.config.fpRegCount →
      arm8Target.getFpReg t j = s2.fpRegs j := by
    intro j hj
    simp only [arm8Target_config, arm8Config] at hj
    omega
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    rw [show arm8Next^[0 + 1] ms = t by
      rw [Nat.zero_add, Function.iterate_one, hnext]]
    exact ⟨hq1, hq2, hq3, hq4, hq5⟩
  refine encoderCaseStep (.inst (.const r v)) s1 s2 ms 0 hs2dom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega

/-! ## The four-`moveWide` shape -/

/-- The `i`-th of four consecutive words is a valid aligned code address. -/
theorem mem_allPcs_four (p : BitVec 64) (i : Nat) (hi : i < 4) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs 16 p 2 := by
  rw [allPcs_eq]
  refine ⟨i, ?_, rfl⟩
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  omega

/-- One constructor of `encoder_correct arm8Target` from the four-`moveWide`
lowering: the four `arm8Next` steps insert the four 16-bit chunks of `v` into the
destination register one at a time, and `locTemp_chain` (the `moveWide`
machinery of `Machine/ControlCase.lean`) reproduces `v`. -/
theorem constCaseFour (r : Nat) (v : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.const r v)) s2 ∧ targetStateRel arm8Target s1 ms)
    (hast : arm8Ast (.inst (.const r v)) =
      [.moveWide .k 0 (v.toNat % 65536) r,
       .moveWide .k 1 ((v >>> 16).toNat % 65536) r,
       .moveWide .k 2 ((v >>> 32).toNat % 65536) r,
       .moveWide .k 3 ((v >>> 48).toNat % 65536) r])
    (hlen : (arm8Enc (.inst (.const r v))).length = 16) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  have st := arm8Start (.inst (.const r v)) s1 s2 ms h
  have hok : asmRegOkExact r arm8Config = true := by
    simpa only [asmOkExact, asmInstOkExact] using st.asmOk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm hok
  have hbytes : bytesInMemoryHOL ms.pc
      ([.moveWide .k 0 (v.toNat % 65536) r,
        .moveWide .k 1 ((v >>> 16).toNat % 65536) r,
        .moveWide .k 2 ((v >>> 32).toNat % 65536) r,
        .moveWide .k 3 ((v >>> 48).toNat % 65536) r].flatMap encodeBytes)
      ms.mem s1.memDomain := by
    have hb := st.bytes
    rwa [arm8Enc, hast] at hb
  rw [bytesInMemory_cons, bytesInMemory_cons, bytesInMemory_cons, bytesInMemory_one]
    at hbytes
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbytes
  let t1 : Arm8State :=
    { ms with regs := (fun j => if j = r then wstep (ms.regs r) 0 (v.toNat % 65536)
        else ms.regs j), pc := ms.pc + 4 }
  let t2 : Arm8State :=
    { t1 with regs := (fun j => if j = r then wstep (t1.regs r) 1 ((v >>> 16).toNat % 65536)
        else t1.regs j), pc := t1.pc + 4 }
  let t3 : Arm8State :=
    { t2 with regs := (fun j => if j = r then wstep (t2.regs r) 2 ((v >>> 32).toNat % 65536)
        else t2.regs j), pc := t2.pc + 4 }
  let t4 : Arm8State :=
    { t3 with regs := (fun j => if j = r then wstep (t3.regs r) 3 ((v >>> 48).toNat % 65536)
        else t3.regs j), pc := t3.pc + 4 }
  have hstep1 : arm8Next ms = t1 := by
    rw [arm8Next_moveWide ms s1.memDomain .k 0 (v.toNat % 65536) r (by decide)
      (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt hb1, execInsn_moveWideK]
    have hreg : readReg { ms with pc := ms.pc + 4 } r = ms.regs r := by
      simp only [readReg, ite_eq_right hne31]
    simp only [hreg, writeReg, ite_eq_right hne31, wstep, t1]
  have hstep2 : arm8Next t1 = t2 := by
    rw [arm8Next_moveWide t1 s1.memDomain .k 1 ((v >>> 16).toNat % 65536) r (by decide)
      (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt hb2, execInsn_moveWideK]
    have hreg : readReg { t1 with pc := t1.pc + 4 } r = t1.regs r := by
      simp only [readReg, ite_eq_right hne31]
    simp only [hreg, writeReg, ite_eq_right hne31, wstep, t2]
  have hstep3 : arm8Next t2 = t3 := by
    rw [arm8Next_moveWide t2 s1.memDomain .k 2 ((v >>> 32).toNat % 65536) r (by decide)
      (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt hb3, execInsn_moveWideK]
    have hreg : readReg { t2 with pc := t2.pc + 4 } r = t2.regs r := by
      simp only [readReg, ite_eq_right hne31]
    simp only [hreg, writeReg, ite_eq_right hne31, wstep, t3]
  have hstep4 : arm8Next t3 = t4 := by
    rw [arm8Next_moveWide t3 s1.memDomain .k 3 ((v >>> 48).toNat % 65536) r (by decide)
      (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt hb4, execInsn_moveWideK]
    have hreg : readReg { t3 with pc := t3.pc + 4 } r = t3.regs r := by
      simp only [readReg, ite_eq_right hne31]
    simp only [hreg, writeReg, ite_eq_right hne31, wstep, t4]
  have hit1 : arm8Next^[1] ms = t1 := by
    rw [Function.iterate_one]; exact hstep1
  have hit2 : arm8Next^[2] ms = t2 := by
    rw [show (2 : Nat) = Nat.succ 1 by rfl, Function.iterate_succ_apply', hit1, hstep2]
  have hit3 : arm8Next^[3] ms = t3 := by
    rw [show (3 : Nat) = Nat.succ 2 by rfl, Function.iterate_succ_apply', hit2, hstep3]
  have hit4 : arm8Next^[4] ms = t4 := by
    rw [show (4 : Nat) = Nat.succ 3 by rfl, Function.iterate_succ_apply', hit3, hstep4]
  have hstepSafe1 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.moveWide .k 0 (v.toNat % 65536) r)
      ((encodeInsn (.moveWide .k 0 (v.toNat % 65536) r)).getD 0) hb1 rfl
      (decode_encode_moveWideInsn .k 0 (v.toNat % 65536) r (by decide)
        (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt) (by rfl)
  have hstepSafe2 : StepSafe s1.memDomain t1 :=
    stepSafe_of_encode t1 s1.memDomain (.moveWide .k 1 ((v >>> 16).toNat % 65536) r)
      ((encodeInsn (.moveWide .k 1 ((v >>> 16).toNat % 65536) r)).getD 0) hb2 rfl
      (decode_encode_moveWideInsn .k 1 ((v >>> 16).toNat % 65536) r (by decide)
        (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt) (by rfl)
  have hstepSafe3 : StepSafe s1.memDomain t2 :=
    stepSafe_of_encode t2 s1.memDomain (.moveWide .k 2 ((v >>> 32).toNat % 65536) r)
      ((encodeInsn (.moveWide .k 2 ((v >>> 32).toNat % 65536) r)).getD 0) hb3 rfl
      (decode_encode_moveWideInsn .k 2 ((v >>> 32).toNat % 65536) r (by decide)
        (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt) (by rfl)
  have hstepSafe4 : StepSafe s1.memDomain t3 :=
    stepSafe_of_encode t3 s1.memDomain (.moveWide .k 3 ((v >>> 48).toNat % 65536) r)
      ((encodeInsn (.moveWide .k 3 ((v >>> 48).toNat % 65536) r)).getD 0) hb4 rfl
      (decode_encode_moveWideInsn .k 3 ((v >>> 48).toNat % 65536) r (by decide)
        (Nat.mod_lt _ (show 0 < 2 ^ 16 by decide)) hlt) (by rfl)
  have hpc1 : t1.pc = ms.pc + 4 := rfl
  have hpc2 : t2.pc = ms.pc + BitVec.ofNat 64 (2 * 4) := by
    rw [show t2.pc = t1.pc + 4 from rfl, hpc1, BitVec.add_assoc]
    rfl
  have hpc3 : t3.pc = ms.pc + BitVec.ofNat 64 (3 * 4) := by
    rw [show t3.pc = t2.pc + 4 from rfl, hpc2, BitVec.add_assoc]
    rfl
  have hpc4 : t4.pc = ms.pc + BitVec.ofNat 64 (4 * 4) := by
    rw [show t4.pc = t3.pc + 4 from rfl, hpc3, BitVec.add_assoc]
    rfl
  have hal1 : holAligned 2 t1.pc = true := by
    rw [show t1.pc = ms.pc + 4 from rfl, (alignedAddSub 2 ms.pc 4 holAligned_four).1,
      st.aligned]
  have hal2 : holAligned 2 t2.pc = true := by
    rw [show t2.pc = t1.pc + 4 from rfl, (alignedAddSub 2 t1.pc 4 holAligned_four).1, hal1]
  have hal3 : holAligned 2 t3.pc = true := by
    rw [show t3.pc = t2.pc + 4 from rfl, (alignedAddSub 2 t2.pc 4 holAligned_four).1, hal2]
  have hal4 : holAligned 2 t4.pc = true := by
    rw [show t4.pc = t3.pc + 4 from rfl, (alignedAddSub 2 t3.pc 4 holAligned_four).1, hal3]
  have hm1 : ∀ j, t1.mem j = ms.mem j := fun _ => rfl
  have hm2 : ∀ j, t2.mem j = ms.mem j := fun _ => rfl
  have hm3 : ∀ j, t3.mem j = ms.mem j := fun _ => rfl
  have hm4 : ∀ j, t4.mem j = ms.mem j := fun _ => rfl
  have hq2 : t1.regs r = wstep (ms.regs r) 0 (v.toNat % 65536) := by
    simp only [t1, ite_true]
  have hq3 : t2.regs r = wstep (t1.regs r) 1 ((v >>> 16).toNat % 65536) := by
    simp only [t2, ite_true]
  have hq4 : t3.regs r = wstep (t2.regs r) 2 ((v >>> 32).toNat % 65536) := by
    simp only [t3, ite_true]
  have hq5 : t4.regs r = wstep (t3.regs r) 3 ((v >>> 48).toNat % 65536) := by
    simp only [t4, ite_true]
  have ht4r : t4.regs r = v := by
    rw [hq5, hq4, hq3, hq2, wstep_zero, wstep_eq_locTemp _ v 1 _ (by rfl),
      wstep_eq_locTemp _ v 2 _ (by rfl), wstep_eq_locTemp _ v 3 _ (by rfl)]
    exact locTemp_chain _ v
  have hx1 : ∀ j, j ≠ r → t1.regs j = ms.regs j := by
    intro j hj; simp only [t1, ite_eq_right hj]
  have hx2 : ∀ j, j ≠ r → t2.regs j = t1.regs j := by
    intro j hj; simp only [t2, ite_eq_right hj]
  have hx3 : ∀ j, j ≠ r → t3.regs j = t2.regs j := by
    intro j hj; simp only [t3, ite_eq_right hj]
  have hx4 : ∀ j, j ≠ r → t4.regs j = t3.regs j := by
    intro j hj; simp only [t4, ite_eq_right hj]
  have hupd : asmUpd (.inst (.const r v)) (s1.pc + BitVec.ofNat 64 16) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 16 := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j = (if j = r then v else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc, updReg]
  have hcode : allPcs (arm8Target.config.encode (.inst (.const r v))).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hf1 : t1.failed = ms.failed := rfl
  have hf2 : t2.failed = ms.failed := rfl
  have hf3 : t3.failed = ms.failed := rfl
  have hf4 : t4.failed = ms.failed := rfl
  have hqA : arm8Target.stateOk t4 = true :=
    arm8StateOk_set t4 hal4 (hf4.trans st.msFailed)
  have hqB : t4.pc = s2.pc := by
    rw [hpc4, st.pc, hs2pc]
    bv_omega
  have hqC : ∀ x, s2.memDomain x → t4.mem x = s2.mem x := by
    intro x hx
    rw [hm4 x, hs2mem x]
    exact st.mem x (hs2dom ▸ hx)
  have hqD : ∀ j, j < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains j = false → t4.regs j = s2.regs j := by
    intro j hj
    by_cases hjr : j = r
    · rw [hjr, ht4r, hs2regs r, ite_eq_left rfl]
    · rw [hx4 j hjr, hx3 j hjr, hx2 j hjr, hx1 j hjr, hs2regs j, ite_eq_right hjr]
      exact st.reg j hj
  have hqE : ∀ j, j < arm8Target.config.fpRegCount →
      arm8Target.getFpReg t4 j = s2.fpRegs j := by
    intro j hj
    simp only [arm8Target_config, arm8Config] at hj
    omega
  have hq : targetStateRel arm8Target s2 (arm8Next^[3 + 1] ms) := by
    rw [show arm8Next^[3 + 1] ms = t4 from hit4]
    exact ⟨hqA, hqB, hqC, hqD, hqE⟩
  refine encoderCaseStep (.inst (.const r v)) s1 s2 ms 3 hs2dom hcode ?_ ?_ hq
  · intro k hk
    interval_cases k
    · simpa using hstepSafe1
    · rw [hit1]; exact hstepSafe2
    · rw [hit2]; exact hstepSafe3
    · rw [hit3]; exact hstepSafe4
  · intro k h1 h2
    interval_cases k
    · rw [hit1]
      exact ⟨arm8StateOk_set _ hal1 st.msFailed, fun pc _ => hm1 pc,
        by rw [hpc1, st.pc, arm8Target_config, arm8Config_encode, hlen]
           exact mem_allPcs_four s1.pc 1 (by norm_num)⟩
    · rw [hit2]
      exact ⟨arm8StateOk_set _ hal2 st.msFailed, fun pc _ => hm2 pc,
        by rw [hpc2, st.pc, arm8Target_config, arm8Config_encode, hlen]
           exact mem_allPcs_four s1.pc 2 (by norm_num)⟩
    · rw [hit3]
      exact ⟨arm8StateOk_set _ hal3 st.msFailed, fun pc _ => hm3 pc,
        by rw [hpc3, st.pc, arm8Target_config, arm8Config_encode, hlen]
           exact mem_allPcs_four s1.pc 3 (by norm_num)⟩

/-! ## The `const` case -/

/-- The `.const r v` constructor of `encoder_correct arm8Target`, by the four
shapes of `arm8_ast`. -/
theorem case_const (r : Nat) (v : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.const r v)) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.const r v)) s1 s2 ms := by
  have st := arm8Start (.inst (.const r v)) s1 s2 ms h
  have hok : asmRegOkExact r arm8Config = true := by
    simpa only [asmOkExact, asmInstOkExact] using st.asmOk
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm hok
  cases hz : encMovImm v with
  | some p =>
    obtain ⟨imm16, hw⟩ := p
    -- the zeroing `moveWide`
    have hast := arm8Ast_const_movZ r v imm16 hw hz
    obtain ⟨hhw, himm⟩ := encMovImm_some_lt v imm16 hw hz
    have hb : bytesInMemoryHOL ms.pc (encodeBytes (.moveWide .z hw imm16 r)) ms.mem
        s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    let t : Arm8State := execInsn { ms with pc := ms.pc + 4 } (.moveWide .z hw imm16 r)
    have hnext : arm8Next ms = t :=
      arm8Next_moveWide ms s1.memDomain .z hw imm16 r hhw himm hlt hb
    have hval := encMovImm_some_val v imm16 hw hz
    have htval : t.regs r = v := by
      simp only [t, execInsn, writeReg, ite_eq_right hne31, hval, ite_true]
    have htpc : t.pc = ms.pc + 4 := by
      simp only [t, execInsn, writeReg, ite_eq_right hne31]
    have htmem : ∀ x, t.mem x = ms.mem x := by
      intro x
      simp only [t, execInsn, writeReg, ite_eq_right hne31]
    have htreg : ∀ j, j ≠ r → t.regs j = ms.regs j := by
      intro j hj
      simp only [t, execInsn, writeReg, ite_eq_right hne31, ite_eq_right hj]
    have htfailed : t.failed = ms.failed := by
      simp only [t, execInsn, writeReg, ite_eq_right hne31]
    have htal : holAligned 2 t.pc = true := by
      rw [htpc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain (.moveWide .z hw imm16 r)
        ((encodeInsn (.moveWide .z hw imm16 r)).getD 0) hb rfl
        (decode_encode_moveWideInsn .z hw imm16 r hhw himm hlt) (by rfl)
    exact constCaseOne r v (.moveWide .z hw imm16 r) t s1 s2 ms h hast hnext htpc htmem htreg
      htval htfailed htal hsafe0
  | none =>
    cases hn : encMovImm (~~~v) with
    | some p =>
      obtain ⟨imm16, hw⟩ := p
      -- the negating `moveWide`
      have hast := arm8Ast_const_movN r v imm16 hw hz hn
      obtain ⟨hhw, himm⟩ := encMovImm_some_lt (~~~v) imm16 hw hn
      have hb : bytesInMemoryHOL ms.pc (encodeBytes (.moveWide .n hw imm16 r)) ms.mem
          s1.memDomain := by
        have hb' := st.bytes
        rw [arm8Enc, hast] at hb'
        simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
      let t : Arm8State := execInsn { ms with pc := ms.pc + 4 } (.moveWide .n hw imm16 r)
      have hnext : arm8Next ms = t :=
        arm8Next_moveWide ms s1.memDomain .n hw imm16 r hhw himm hlt hb
      have hval := encMovImm_some_val_not v imm16 hw hn
      have htval : t.regs r = v := by
        simp only [t, execInsn, writeReg, ite_eq_right hne31, hval, ite_true]
      have htpc : t.pc = ms.pc + 4 := by
        simp only [t, execInsn, writeReg, ite_eq_right hne31]
      have htmem : ∀ x, t.mem x = ms.mem x := by
        intro x
        simp only [t, execInsn, writeReg, ite_eq_right hne31]
      have htreg : ∀ j, j ≠ r → t.regs j = ms.regs j := by
        intro j hj
        simp only [t, execInsn, writeReg, ite_eq_right hne31, ite_eq_right hj]
      have htfailed : t.failed = ms.failed := by
        simp only [t, execInsn, writeReg, ite_eq_right hne31]
      have htal : holAligned 2 t.pc = true := by
        rw [htpc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain (.moveWide .n hw imm16 r)
          ((encodeInsn (.moveWide .n hw imm16 r)).getD 0) hb rfl
          (decode_encode_moveWideInsn .n hw imm16 r hhw himm hlt) (by rfl)
      exact constCaseOne r v (.moveWide .n hw imm16 r) t s1 s2 ms h hast hnext htpc htmem
        htreg htval htfailed htal hsafe0
    | none =>
      by_cases hbm : (encodeBitMask v).isSome = true
      · -- the bitmask `logicalImmediate`
        obtain ⟨⟨n, imms, immr⟩, hbits⟩ := Option.isSome_iff_exists.mp hbm
        have hast := arm8Ast_const_orr r v hz hn hbm
        have hb : bytesInMemoryHOL ms.pc (encodeBytes (.logicalImmediate .orr false v 31 r))
            ms.mem s1.memDomain := by
          have hb' := st.bytes
          rw [arm8Enc, hast] at hb'
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
        let t : Arm8State := execInsn { ms with pc := ms.pc + 4 }
          (.logicalImmediate .orr false v 31 r)
        have hnext : arm8Next ms = t :=
          arm8Next_logicalImmediate ms s1.memDomain .orr false v 31 r 1 n imms immr
            (by decide) hbits (by decide) hlt hb
        have htval : t.regs r = v := by
          simp only [t, execInsn, writeReg, ite_eq_right hne31, Bool.false_eq_true, ite_false,
            readReg, ite_true]
          change (0#64) ||| v = v
          exact BitVec.zero_or
        have htpc : t.pc = ms.pc + 4 := by
          simp only [t, execInsn, writeReg, ite_eq_right hne31, Bool.false_eq_true, ite_false]
        have htmem : ∀ x, t.mem x = ms.mem x := by
          intro x
          simp only [t, execInsn, writeReg, ite_eq_right hne31, Bool.false_eq_true, ite_false]
        have htreg : ∀ j, j ≠ r → t.regs j = ms.regs j := by
          intro j hj
          simp only [t, execInsn, writeReg, ite_eq_right hne31, Bool.false_eq_true, ite_false,
            ite_eq_right hj]
        have htfailed : t.failed = ms.failed := by
          simp only [t, execInsn, writeReg, ite_eq_right hne31, Bool.false_eq_true, ite_false]
        have htal : holAligned 2 t.pc = true := by
          rw [htpc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
        have hsafe0 : StepSafe s1.memDomain ms :=
          stepSafe_of_encode ms s1.memDomain (.logicalImmediate .orr false v 31 r)
            _ hb
            (encodeInsn_logicalImmediate .orr false v 31 r 1 n imms immr (by decide) hbits)
            (decode_encode_logicalImmediate .orr false v 31 r 1 n imms immr (by decide) hbits
              (by decide) hlt) (by rfl)
        exact constCaseOne r v (.logicalImmediate .orr false v 31 r) t s1 s2 ms h hast hnext
          htpc htmem htreg htval htfailed htal hsafe0
      · -- the four `moveWide`s
        have hbmf : (encodeBitMask v).isSome = false := boolOfNotTrue hbm
        have hast := arm8Ast_const_movK r v hz hn hbmf
        have hlen : (arm8Enc (.inst (.const r v))).length = 16 := by
          rw [arm8Enc, hast]
          simp [encodeBytes_length]
        exact constCaseFour r v s1 s2 ms h hast hlen

end Flapjack.Compiler.Encoders.Arm8
