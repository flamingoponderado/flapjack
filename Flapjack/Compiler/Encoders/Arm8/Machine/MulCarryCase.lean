/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.ShiftCaseFull

/-!
# The ARM8 `longMul`, carry/overflow and unavailable-operation cases

`Machine/Target.lean` lowers the arithmetic forms that the earlier
`Machine/*Case.lean` files do not cover to short instruction sequences:

* `longMul` becomes `MULH x, y` followed by `MADD` of the low half into the
  second destination;
* `addCarry` becomes a five-instruction `ADDS`/`CCMP`/`ADCS`/`MOV`/`ADC`
  sequence that threads the carry of the source state through the `C` flag and
  finally moves it into the result register;
* `addOverflow`/`subOverflow` become an `ADDS`/`SUBS` that sets the `V` flag
  followed by a conditional select of `1`/`0` under the condition `!V`;
* `longDiv` and `fp` lower to `noOp`, and are rejected by `asmArithOkExact`/
  `asmFpOkExact` under `arm8Config`, so no `asmStep` reaches them.  Note that
  `HolArith.longDiv` carries five explicit `Nat` fields here (there is no
  `LongDiv` payload type in Flapjack), so the two vacuous cases quantify over
  five and one arguments respectively.

Each case is the `CaseGoal` of `encoder_correct arm8Target` reduced through
`encoderCaseStep` to the interference-free run of `arm8Next` (`n` steps for an
`n + 1`-instruction lowering), as in `Machine/ControlCase.lean`.  The
intermediate states are named definitions below so that each run step is a
`rfl`-level consequence of the corresponding decoder lemma.

The flag values of the conditional-compare/conditional-select sequence are read
off `execInsn` directly: `ADDS xzr, ry, #0` writes the flags of `ry - 0`
(`N = msb ry`, `Z = (ry = 0)`, `C = true`, `V = false`), `CCMP rz, #0, EQ, nzcv =
(F,F,T,F)` writes the flags of `rz + 0` when `Z` holds and `(F,F,T,F)` otherwise
(so `C = (ry ≠ 0)`), and `ADCS`/`ADC` therefore compute
`readReg resultCarry + readReg sourceLeft + (if readReg sourceRight = 0 then 0
else 1)`, which is exactly the `arithUpd` clause.

As in the other `Machine/*Case.lean` files, this is a case split of the single
HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`Inst`/`Arith` branch has no per-case declaration of its own; the module is
Flapjack infrastructure and carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Peeling instruction lists -/

/-- Splitting two four-byte instructions off a `bytesInMemoryHOL` fact. -/
theorem bytesInMemory_two (pc : BitVec 64) (i1 i2 : Insn)
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc ([i1, i2].flatMap encodeBytes) m dm ↔
      bytesInMemoryHOL pc (encodeBytes i1) m dm ∧
        bytesInMemoryHOL (pc + 4) (encodeBytes i2) m dm := by
  rw [bytesInMemory_cons, bytesInMemory_one]

/-- Splitting five four-byte instructions off a `bytesInMemoryHOL` fact. -/
theorem bytesInMemory_five (pc : BitVec 64) (i1 i2 i3 i4 i5 : Insn)
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc ([i1, i2, i3, i4, i5].flatMap encodeBytes) m dm ↔
      bytesInMemoryHOL pc (encodeBytes i1) m dm ∧
      bytesInMemoryHOL (pc + 4) (encodeBytes i2) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4) (encodeBytes i3) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4 + 4) (encodeBytes i4) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4 + 4 + 4) (encodeBytes i5) m dm := by
  rw [bytesInMemory_cons, bytesInMemory_cons, bytesInMemory_cons, bytesInMemory_cons,
    bytesInMemory_one]

/-- The `i`-th of `n` four-byte words at `p` is in the stride-`4` PC set. -/
theorem mem_allPcs_step4 (n i : Nat) (p : BitVec 64) (h : i * 4 < n) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs n p 2 := by
  rw [allPcs_eq]
  exact ⟨i, by simpa using h, rfl⟩

/-! ## Machine-state field projections -/

/-- `writeReg` never moves the program counter. -/
theorem writeReg_pc (s : Arm8State) (r : Nat) (v : BitVec 64) : (writeReg s r v).pc = s.pc := by
  simp only [writeReg]
  split <;> rfl

/-- `writeReg` never changes memory. -/
theorem writeReg_mem_apply (s : Arm8State) (r : Nat) (v : BitVec 64) (x : BitVec 64) :
    (writeReg s r v).mem x = s.mem x := by
  simp only [writeReg]
  split <;> rfl

/-- `writeReg` never changes the failure flag. -/
theorem writeReg_failed (s : Arm8State) (r : Nat) (v : BitVec 64) :
    (writeReg s r v).failed = s.failed := by
  simp only [writeReg]
  split <;> rfl

/-- The register file after a `writeReg` of a non-zero register. -/
theorem writeReg_regs (s : Arm8State) {r : Nat} (hne : r ≠ 31) (v : BitVec 64) (j : Nat) :
    (writeReg s r v).regs j = (if j = r then v else s.regs j) := by
  simp only [writeReg, ite_eq_right hne]

/-- Reading a register after advancing the PC. -/
theorem readReg_pcUpdate (s : Arm8State) (pc : BitVec 64) (r : Nat) :
    readReg { s with pc := pc } r = readReg s r := rfl

/-- `writeFlags` only changes the four flags. -/
theorem writeFlags_pc (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).pc = s.pc := rfl

theorem writeFlags_mem_apply (s : Arm8State) (f : Arm8Flags) (x : BitVec 64) :
    (writeFlags s f).mem x = s.mem x := rfl

theorem writeFlags_failed (s : Arm8State) (f : Arm8Flags) :
    (writeFlags s f).failed = s.failed := rfl

theorem writeFlags_regs (s : Arm8State) (f : Arm8Flags) :
    (writeFlags s f).regs = s.regs := rfl

theorem writeFlags_z (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).z = f.2.1 := rfl

theorem writeFlags_c (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).c = f.2.2.1 := rfl

theorem writeFlags_v (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).v = f.2.2.2 := rfl

theorem writeFlags_n (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).n = f.1 := rfl

/-- A source register of the start relation agrees with the machine file. -/
theorem msRegs (st : Arm8Start i s1 s2 ms) {r : Nat}
    (hlt : r < arm8Config.regCount) (hav : arm8Config.avoidRegs.contains r = false) :
    ms.regs r = s1.regs r :=
  st.reg r (by rw [arm8Target_config]; exact ⟨hlt, hav⟩)

/-! ## The two halves of a 64-bit product -/

/-- The high half of the 128-bit product of two 64-bit words. -/
def mulHi (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)

/-- The low half of a product, in the shape `arithUpd` writes it. -/
def mulLo (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat * y.toNat)

/-- The unsigned 128-bit extension has the same `toNat` as its argument. -/
theorem toNat_setWidth128 (x : BitVec 64) : (x.setWidth 128).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt
    (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- The product of two 64-bit words fits in 128 bits. -/
theorem pow64_mul_pow64 : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num

theorem toNat_mul_lt_pow128 (x y : BitVec 64) : x.toNat * y.toNat < 2 ^ 128 := by
  calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' x.isLt y.isLt
    _ = 2 ^ 128 := pow64_mul_pow64

/-- The high 64 bits of the unsigned 128-bit product are `mulHi`. -/
theorem mulHi_eq (x y : BitVec 64) :
    (x.zeroExtend 128 * y.zeroExtend 128).extractLsb' 64 64 = mulHi x y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, toNat_setWidth128, toNat_setWidth128,
    Nat.mod_eq_of_lt (toNat_mul_lt_pow128 x y), Nat.shiftRight_eq_div_pow,
    mulHi, BitVec.toNat_ofNat]

/-- The 64-bit truncation of the unsigned product is `mulLo`. -/
theorem mulLo_eq (x y : BitVec 64) : x * y = mulLo x y := by
  apply BitVec.eq_of_toNat_eq
  rw [mulLo, BitVec.toNat_mul, BitVec.toNat_ofNat]

/-- Executing the unsigned `MULH` of the `longMul` lowering. -/
theorem execInsn_multiplyHigh_unsigned (s : Arm8State) (rm rn rd : Nat) :
    execInsn s (.multiplyHigh false rm rn rd) =
      writeReg s rd (mulHi (readReg s rn) (readReg s rm)) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]
  rw [mulHi_eq]

/-- Executing the adding `MADD` of the `longMul` lowering. -/
theorem execInsn_multiplyAddSub_add (s : Arm8State) (rm ra rn rd : Nat) :
    execInsn s (.multiplyAddSub false rm ra rn rd) =
      writeReg s rd (readReg s ra + readReg s rn * readReg s rm) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]

/-- The register update of a `longMul`. -/
theorem arithUpd_longMul_regs (s : AsmState 64) (r1 r2 r3 r4 : Nat) :
    ∀ j, (arithUpd (.longMul r1 r2 r3 r4) s).regs j =
      (if j = r2 then mulLo (s.regs r3) (s.regs r4)
       else if j = r1 then mulHi (s.regs r3) (s.regs r4) else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg, mulLo, mulHi]

/-! ## The `longMul` case -/

/-- `arm8_ast` of `longMul`. -/
theorem arm8Ast_longMul (r1 r2 r3 r4 : Nat) :
    arm8Ast (.inst (.arith (.longMul r1 r2 r3 r4))) =
      [.multiplyHigh false r4 r3 r1, .multiplyAddSub false r4 31 r3 r2] := rfl

/-- The `arm8Config` architecture comparisons used by the side conditions. -/
theorem arm8_isa_x86 : (arm8Config.isa == .x86_64) = false := by decide
theorem arm8_isa_armv7 : (arm8Config.isa == .armv7) = false := by decide
theorem arm8_isa_armv8 : (arm8Config.isa == .armv8) = true := by decide
theorem arm8_isa_riscv : (arm8Config.isa == .riscv) = false := by decide
theorem arm8_isa_ag32 : (arm8Config.isa == .ag32) = false := by decide
theorem arm8_isa_mips : (arm8Config.isa == .mips) = false := by decide

/-- The `arm8Config` two-register constraint, which ARMv8 does not impose. -/
theorem arm8_twoRegArith : arm8Config.twoRegArith = false := by decide

/-- The register side conditions of a `longMul`, including the ARMv8
source/destination disjointness of the high half. -/
theorem arithRegOkLongMul (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.longMul r1 r2 r3 r4))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    asmRegOkExact r1 arm8Config = true ∧ asmRegOkExact r2 arm8Config = true ∧
      asmRegOkExact r3 arm8Config = true ∧ asmRegOkExact r4 arm8Config = true ∧
      r1 ≠ r3 ∧ r1 ≠ r4 := by
  have st := arm8Start _ s1 s2 ms h
  have hb := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8_isa_x86, arm8_isa_armv7,
    arm8_isa_armv8, arm8_isa_riscv, arm8_isa_ag32, Bool.not_false, Bool.not_true,
    Bool.false_or, Bool.true_or, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, and_assoc, and_true] at hb
  exact hb

/-- The state after the `MULH` of the `longMul` lowering. -/
def longMulT1 (s1 : AsmState 64) (ms : Arm8State) (r1 r3 r4 : Nat) : Arm8State :=
  writeReg { ms with pc := ms.pc + 4 } r1 (mulHi (s1.regs r3) (s1.regs r4))

/-- The state after the `MADD` of the `longMul` lowering. -/
def longMulT2 (s1 : AsmState 64) (ms : Arm8State) (r1 r2 r3 r4 : Nat) : Arm8State :=
  writeReg { longMulT1 s1 ms r1 r3 r4 with pc := (longMulT1 s1 ms r1 r3 r4).pc + 4 } r2
    (mulLo (s1.regs r3) (s1.regs r4))

/-- The `longMul` constructor of `encoder_correct arm8Target`. -/
theorem case_longMul (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.longMul r1 r2 r3 r4))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.longMul r1 r2 r3 r4))) s1 s2 ms := by
  obtain ⟨hok1, hok2, hok3, hok4, hne13, hne14⟩ :=
    arithRegOkLongMul r1 r2 r3 r4 s1 s2 ms h
  obtain ⟨hlt1, hav1, hne31_1⟩ := regOk_of_asm hok1
  obtain ⟨hlt2, hav2, hne31_2⟩ := regOk_of_asm hok2
  obtain ⟨hlt3, hav3, hne31_3⟩ := regOk_of_asm hok3
  obtain ⟨hlt4, hav4, hne31_4⟩ := regOk_of_asm hok4
  have hne14' : ¬(r4 = r1) := fun hr => hne14 hr.symm
  have hne13' : ¬(r3 = r1) := fun hr => hne13 hr.symm
  have st := arm8Start (.inst (.arith (.longMul r1 r2 r3 r4))) s1 s2 ms h
  have hasm : arm8Ast (.inst (.arith (.longMul r1 r2 r3 r4))) =
      [.multiplyHigh false r4 r3 r1, .multiplyAddSub false r4 31 r3 r2] :=
    arm8Ast_longMul r1 r2 r3 r4
  have hb : bytesInMemoryHOL ms.pc
      ([.multiplyHigh false r4 r3 r1, .multiplyAddSub false r4 31 r3 r2].flatMap
        encodeBytes) ms.mem s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hasm] at hb'
    exact hb'
  obtain ⟨hb1, hb2⟩ := (bytesInMemory_two ms.pc (.multiplyHigh false r4 r3 r1)
    (.multiplyAddSub false r4 31 r3 r2) ms.mem s1.memDomain).1 hb
  have hnext1 : arm8Next ms = longMulT1 s1 ms r1 r3 r4 := by
    rw [arm8Next_multiplyHigh ms s1.memDomain false r4 r3 r1 hlt4 hlt3 hlt1 hb1,
      execInsn_multiplyHigh_unsigned]
    simp only [longMulT1]
    simp only [readReg, ite_eq_right hne31_3, ite_eq_right hne31_4]
    rw [msRegs st hlt3 hav3, msRegs st hlt4 hav4]
  have hnext2 : arm8Next (longMulT1 s1 ms r1 r3 r4) = longMulT2 s1 ms r1 r2 r3 r4 := by
    have hb2' : bytesInMemoryHOL (longMulT1 s1 ms r1 r3 r4).pc
        (encodeBytes (.multiplyAddSub false r4 31 r3 r2)) (longMulT1 s1 ms r1 r3 r4).mem
        s1.memDomain := by
      rw [longMulT1, writeReg_pc, writeReg_mem]
      exact hb2
    rw [arm8Next_multiplyAddSub (longMulT1 s1 ms r1 r3 r4) s1.memDomain false r4 31 r3 r2
      hlt4 (by decide) hlt3 hlt2 hb2', execInsn_multiplyAddSub_add, longMulT2]
    simp only [readReg, ite_true, longMulT1, writeReg_regs _ hne31_1,
      hne31_3, hne31_4, hne13', hne14', ite_false]
    rw [msRegs st hlt3 hav3, msRegs st hlt4 hav4]
    have hval : 0 + s1.regs r3 * s1.regs r4 = mulLo (s1.regs r3) (s1.regs r4) := by
      simp only [mulLo]
      bv_omega
    rw [hval]
  have hlen : (arm8Enc (.inst (.arith (.longMul r1 r2 r3 r4)))).length = 8 := by
    rw [arm8Enc, hasm, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, encodeBytes_length, encodeBytes_length]
  have hupd : asmUpd (.inst (.arith (.longMul r1 r2 r3 r4)))
      (s1.pc + BitVec.ofNat 64 8) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 8 := by
    rw [← hupd]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j =
      (if j = r2 then mulLo (s1.regs r3) (s1.regs r4)
       else if j = r1 then mulHi (s1.regs r3) (s1.regs r4) else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_longMul_regs s1 r1 r2 r3 r4 j
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.multiplyHigh false r4 r3 r1) _ hb1
      (encodeInsn_multiplyHigh false r4 r3 r1)
      (decode_encode_multiplyHigh false r4 r3 r1 hlt4 hlt3 hlt1) (by rfl)
  have hsafe1 : StepSafe s1.memDomain (longMulT1 s1 ms r1 r3 r4) := by
    have hb2' : bytesInMemoryHOL (longMulT1 s1 ms r1 r3 r4).pc
        (encodeBytes (.multiplyAddSub false r4 31 r3 r2)) (longMulT1 s1 ms r1 r3 r4).mem
        s1.memDomain := by
      rw [longMulT1, writeReg_pc, writeReg_mem]
      exact hb2
    exact stepSafe_of_encode (longMulT1 s1 ms r1 r3 r4) s1.memDomain
      (.multiplyAddSub false r4 31 r3 r2) _ hb2'
      (encodeInsn_multiplyAddSub false r4 31 r3 r2)
      (decode_encode_multiplyAddSub false r4 31 r3 r2 hlt4 (by decide) hlt3 hlt2) (by rfl)
  have hcode : allPcs (arm8Target.config.encode (.inst (.arith (.longMul r1 r2 r3 r4)))).length
      s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc, hlen]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hal4 : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
  have hal8 : holAligned 2 (8 : BitVec 64) = true := aligned_of_mod 8 (by decide)
  have hq : targetStateRel arm8Target s2 (arm8Next^[1 + 1] ms) := by
    have hit : arm8Next^[1 + 1] ms = longMulT2 s1 ms r1 r2 r3 r4 := by
      rw [Function.iterate_succ_apply, Function.iterate_one, hnext1, hnext2]
    rw [hit]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show arm8StateOk (longMulT2 s1 ms r1 r2 r3 r4) = true
      refine arm8StateOk_set _ ?_ ?_
      · rw [longMulT2, writeReg_pc, longMulT1, writeReg_pc,
          (alignedAddSub 2 (ms.pc + 4) 4 hal4).1, (alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
      · rw [longMulT2, writeReg_failed, longMulT1, writeReg_failed]
        exact st.msFailed
    · show (longMulT2 s1 ms r1 r2 r3 r4).pc = s2.pc
      rw [longMulT2, writeReg_pc, longMulT1, writeReg_pc, st.pc, hs2pc]
      bv_omega
    · intro x hx
      show (longMulT2 s1 ms r1 r2 r3 r4).mem x = s2.mem x
      rw [longMulT2, writeReg_mem, longMulT1, writeReg_mem, hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro j hj
      have hget : arm8Target.getReg (longMulT2 s1 ms r1 r2 r3 r4) j
          = (longMulT2 s1 ms r1 r2 r3 r4).regs j := rfl
      rw [hget]
      have hs := hs2regs j
      simp only [longMulT2, longMulT1, writeReg_regs _ hne31_2, writeReg_regs _ hne31_1]
      by_cases hj2 : j = r2
      · rw [ite_eq_left hj2] at hs ⊢
        exact hs.symm
      · rw [ite_eq_right hj2] at hs ⊢
        by_cases hj1 : j = r1
        · rw [ite_eq_left hj1] at hs ⊢
          exact hs.symm
        · rw [ite_eq_right hj1] at hs ⊢
          rw [st.reg j hj]
          exact hs.symm
    · intro j hj
      simp only [arm8Target_config, arm8Config] at hj
      omega
  refine encoderCaseStep (.inst (.arith (.longMul r1 r2 r3 r4))) s1 s2 ms 1 hs2dom hcode ?_ ?_ hq
  · intro k hk
    interval_cases k
    · simpa using hsafe0
    · simpa [Function.iterate_one, hnext1] using hsafe1
  · intro k h1 h2
    have hk1 : k = 1 := by omega
    subst hk1
    have hit : arm8Next^[1] ms = longMulT1 s1 ms r1 r3 r4 := by
      rw [Function.iterate_one, hnext1]
    rw [hit]
    refine ⟨?_, ?_, ?_⟩
    · refine arm8StateOk_set _ ?_ ?_
      · rw [longMulT1, writeReg_pc, (alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
      · rw [longMulT1, writeReg_failed]
        exact st.msFailed
    · intro pc _
      rw [longMulT1, writeReg_mem]
    · have hmem : s1.pc + BitVec.ofNat 64 (1 * 4) ∈ allPcs 8 s1.pc 2 :=
        mem_allPcs_step4 8 1 s1.pc (by norm_num)
      simpa [longMulT1, writeReg_pc, st.pc, arm8Target_config, arm8Config, arm8Config_encode,
        hlen] using hmem


/-! ## The `addWithCarry` shapes of the remaining lowerings -/

/-- Writing the zero register leaves the state unchanged. -/
theorem writeReg_zero_reg (s : Arm8State) (v : BitVec 64) : writeReg s 31 v = s := by
  simp only [writeReg, ite_true]

/-- The condition flags after writing a register. -/
theorem writeReg_c (s : Arm8State) (r : Nat) (v : BitVec 64) : (writeReg s r v).c = s.c := by
  simp only [writeReg]; split <;> rfl

/-- The overflow flag after writing a register. -/
theorem writeReg_v (s : Arm8State) (r : Nat) (v : BitVec 64) : (writeReg s r v).v = s.v := by
  simp only [writeReg]; split <;> rfl

/-- A `Bool`-valued `if` over a `decide`d proposition. -/
theorem ite_decide_eq {α : Type} (P : Prop) [Decidable P] (a b : α) :
    (if decide P then a else b) = if P then a else b := by
  by_cases h : P <;> simp [h]

/-- The value `addWithCarry` produces. -/
theorem addWithCarry_val (x y : BitVec 64) (cin : Bool) :
    (addWithCarry x y cin).1 = x + y + (if cin then 1 else 0) := by
  cases cin with
  | false =>
    rw [arith_addWithCarry_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    bv_omega
  | true =>
    rw [arith_addWithCarry_true]
    simp only [↓reduceIte]

/-- The flags `addWithCarry` produces, in terms of its own result. -/
theorem addWithCarry_flags (x y : BitVec 64) (cin : Bool) :
    (addWithCarry x y cin).2 =
      ((addWithCarry x y cin).1.getLsbD 63, decide ((addWithCarry x y cin).1 = 0),
       decide ((addWithCarry x y cin).1.toNat ≠ x.toNat + y.toNat + (if cin then 1 else 0)),
       decide ((addWithCarry x y cin).1.toInt ≠ x.toInt + y.toInt + (if cin then 1 else 0))) :=
  rfl

/-- The flags of a flag-setting addition without carry. -/
def addFlags (x y : BitVec 64) : Arm8Flags :=
  let r := x + y
  (r.getLsbD 63, decide (r = 0), decide (r.toNat ≠ x.toNat + y.toNat),
    decide (r.toInt ≠ x.toInt + y.toInt))

/-- The flags of a flag-setting subtraction. -/
def subFlags (x y : BitVec 64) : Arm8Flags :=
  let r := x - y
  (r.getLsbD 63, decide (r = 0), decide (r.toNat ≠ x.toNat + (~~~y).toNat + 1),
    decide (r.toInt ≠ x.toInt + (~~~y).toInt + 1))

/-- `addWithCarry` on an uncomplemented second operand, without carry. -/
theorem addWithCarry_addFlags (x y : BitVec 64) :
    addWithCarry x y false = (x + y, addFlags x y) := by
  refine Prod.ext ?_ ?_
  · show (addWithCarry x y false).1 = x + y
    rw [arith_addWithCarry_false]
  · show (addWithCarry x y false).2 = addFlags x y
    rw [addWithCarry_flags, arith_addWithCarry_false]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero, Nat.add_zero, addFlags]

/-- `addWithCarry` on a complemented second operand, with carry. -/
theorem addWithCarry_subFlags (x y : BitVec 64) :
    addWithCarry x (~~~y) true = (x - y, subFlags x y) := by
  refine Prod.ext ?_ ?_
  · show (addWithCarry x (~~~y) true).1 = x - y
    rw [arith_addWithCarry_true, arith_add_not_add_one]
  · show (addWithCarry x (~~~y) true).2 = subFlags x y
    rw [addWithCarry_flags, arith_addWithCarry_true, arith_add_not_add_one]
    simp only [↓reduceIte, subFlags]

/-- The overflow flag of a flag-setting addition. -/
theorem addFlags_v (x y : BitVec 64) :
    (addFlags x y).2.2.2 = decide ((x + y).toInt ≠ x.toInt + y.toInt) := rfl

/-- The overflow flag of a flag-setting subtraction. -/
theorem subFlags_v (x y : BitVec 64) :
    (subFlags x y).2.2.2 = decide ((x - y).toInt ≠ x.toInt - y.toInt) := by
  have h : x.toInt + (~~~y).toInt + 1 = x.toInt - y.toInt := by
    rw [jumpCmp_toInt_not]; omega
  rw [subFlags, h]

/-- Executing the flag-setting addition of the `addOverflow` lowering. -/
theorem execInsn_overflowAdd (s : Arm8State) (sl c d : Nat) :
    execInsn s (.addSubShiftedRegister false true .lsl sl 0 c d) =
      writeReg (writeFlags s (addFlags (readReg s c) (readReg s sl))) d
        (readReg s c + readReg s sl) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte, shiftValue, Nat.zero_mod,
    BitVec.shiftLeft_zero, addWithCarry_addFlags]

/-- Executing the flag-setting subtraction of the `subOverflow` lowering. -/
theorem execInsn_overflowSub (s : Arm8State) (sl c d : Nat) :
    execInsn s (.addSubShiftedRegister true true .lsl sl 0 c d) =
      writeReg (writeFlags s (subFlags (readReg s c) (readReg s sl))) d
        (readReg s c - readReg s sl) := by
  simp only [execInsn, ↓reduceIte, shiftValue, Nat.zero_mod, BitVec.shiftLeft_zero,
    addWithCarry_subFlags]

/-- Executing the conditional select that materialises an overflow flag. -/
theorem execInsn_conditionalSelect_v (s : Arm8State) (u : Nat) :
    execInsn s (.conditionalSelect false true 7 31 31 u) =
      writeReg s u (if s.v then 1 else 0) := by
  have h01 : (0 : BitVec 64) + 1 = 1 := by decide
  cases hv : s.v with
  | false => simp only [execInsn, conditionHolds, hv, Bool.not_false, readReg,
      Bool.false_eq_true, ↓reduceIte]
  | true => simp only [execInsn, conditionHolds, hv, Bool.not_true, readReg,
      Bool.false_eq_true, ↓reduceIte, h01]

/-! ## The `n + 1`-instruction `arith` run -/

/-- A `CaseGoal` for a lowering of `n + 1` instructions from its interference-free
run: `t` lists the state before each instruction, with `t 0 = ms`. -/
theorem arithRunCase (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : Arm8State) (n : Nat)
    (t : Nat → Arm8State)
    (h : asmStep arm8Config s1 i s2 ∧ targetStateRel arm8Target s1 ms)
    (ht0 : t 0 = ms)
    (hlen : (arm8Enc i).length = (n + 1) * 4)
    (hstep : ∀ k, k ≤ n → arm8Next (t k) = t (k + 1))
    (hstate : ∀ k, 1 ≤ k → k ≤ n → arm8StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧
      (t k).pc = ms.pc + BitVec.ofNat 64 (k * 4))
    (hsafe : ∀ k, k ≤ n → StepSafe s1.memDomain (t k))
    (hs2dom : s2.memDomain = s1.memDomain)
    (hq : targetStateRel arm8Target s2 (t (n + 1))) :
    CaseGoal i s1 s2 ms := by
  have st := arm8Start i s1 s2 ms h
  have hcode : allPcs (arm8Target.config.encode i).length s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc, hlen]
    rw [show (n + 1) * 4 = (arm8Enc i).length from hlen.symm]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hlen' : (arm8Target.config.encode i).length = (n + 1) * 4 := by
    rw [arm8Target_config, arm8Config_encode, hlen]
  have hit : ∀ k, k ≤ n + 1 → arm8Next^[k] ms = t k := by
    intro k hk
    induction k with
    | zero => rw [Function.iterate_zero]; exact ht0.symm
    | succ m ih => rw [Function.iterate_succ_apply', ih (by omega), hstep m (by omega)]
  refine encoderCaseStep i s1 s2 ms n hs2dom hcode ?_ ?_ ?_
  · intro k hk
    rw [hit k (by omega)]
    exact hsafe k hk
  · intro k h1 h2
    obtain ⟨hok, hmem, hpc⟩ := hstate k h1 h2
    rw [hit k (by omega)]
    refine ⟨hok, ?_, ?_⟩
    · intro pc _
      exact hmem pc
    · rw [hpc, st.pc, hlen', arm8Target_config, arm8Config]
      exact mem_allPcs_step4 ((n + 1) * 4) k s1.pc
        (Nat.mul_lt_mul_of_pos_right (by omega) (by norm_num))
  · rw [hit (n + 1) (by omega)]
    exact hq

/-! ## The `addOverflow` and `subOverflow` cases -/

/-- The register side conditions of an overflow-shaped `arith` operation. -/
theorem arithRegOkOverflow {op : HolArith 64} {r1 r2 r3 r4 : Nat}
    (hop : op = .addOverflow r1 r2 r3 r4 ∨ op = .subOverflow r1 r2 r3 r4)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith op)) s2 ∧ targetStateRel arm8Target s1 ms) :
    asmRegOkExact r1 arm8Config = true ∧ asmRegOkExact r2 arm8Config = true ∧
      asmRegOkExact r3 arm8Config = true ∧ asmRegOkExact r4 arm8Config = true := by
  have hb := (arm8Start _ s1 s2 ms h).asmOk
  rcases hop with h1 | h1
  · rw [h1] at hb
    simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8_twoRegArith, arm8_isa_mips,
      arm8_isa_riscv, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_eq_true,
      and_assoc, true_and, and_true] at hb
    exact hb
  · rw [h1] at hb
    simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8_twoRegArith, arm8_isa_mips,
      arm8_isa_riscv, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_eq_true,
      and_assoc, true_and, and_true] at hb
    exact hb

/-- The register update of an `addOverflow`. -/
theorem arithUpd_addOverflow_regs (s : AsmState 64) (r1 r2 r3 r4 : Nat) :
    ∀ j, (arithUpd (.addOverflow r1 r2 r3 r4) s).regs j =
      (if j = r4 then
        (if (s.regs r2 + s.regs r3).toInt ≠ (s.regs r2).toInt + (s.regs r3).toInt then 1 else 0)
       else if j = r1 then s.regs r2 + s.regs r3 else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg]
  by_cases h4 : j = r4
  · simp only [ite_eq_left h4]
    simp
  · simp only [ite_eq_right h4]

/-- The register update of a `subOverflow`. -/
theorem arithUpd_subOverflow_regs (s : AsmState 64) (r1 r2 r3 r4 : Nat) :
    ∀ j, (arithUpd (.subOverflow r1 r2 r3 r4) s).regs j =
      (if j = r4 then
        (if (s.regs r2 - s.regs r3).toInt ≠ (s.regs r2).toInt - (s.regs r3).toInt then 1 else 0)
       else if j = r1 then s.regs r2 - s.regs r3 else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg]
  by_cases h4 : j = r4
  · simp only [ite_eq_left h4]
    simp
  · simp only [ite_eq_right h4]
/-- The state after the flag-setting addition of the `addOverflow` lowering. -/
def overflowAddT1 (s1 : AsmState 64) (ms : Arm8State) (d c t : Nat) : Arm8State :=
  writeReg (writeFlags { ms with pc := ms.pc + 4 } (addFlags (s1.regs c) (s1.regs t))) d
    (s1.regs c + s1.regs t)

/-- The state after the overflow select of the `addOverflow` lowering. -/
def overflowAddT2 (s1 : AsmState 64) (ms : Arm8State) (d c t u : Nat) : Arm8State :=
  writeReg { overflowAddT1 s1 ms d c t with pc := (overflowAddT1 s1 ms d c t).pc + 4 } u
    (if (overflowAddT1 s1 ms d c t).v then 1 else 0)

/-- The state after the flag-setting subtraction of the `subOverflow` lowering. -/
def overflowSubT1 (s1 : AsmState 64) (ms : Arm8State) (d c t : Nat) : Arm8State :=
  writeReg (writeFlags { ms with pc := ms.pc + 4 } (subFlags (s1.regs c) (s1.regs t))) d
    (s1.regs c - s1.regs t)

/-- The state after the overflow select of the `subOverflow` lowering. -/
def overflowSubT2 (s1 : AsmState 64) (ms : Arm8State) (d c t u : Nat) : Arm8State :=
  writeReg { overflowSubT1 s1 ms d c t with pc := (overflowSubT1 s1 ms d c t).pc + 4 } u
    (if (overflowSubT1 s1 ms d c t).v then 1 else 0)

/-- The `addOverflow` constructor of `encoder_correct arm8Target`. -/
theorem case_addOverflow (destination resultCarry sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1
        (.inst (.arith (.addOverflow destination resultCarry sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.addOverflow destination resultCarry sourceLeft sourceRight)))
      s1 s2 ms := by
  obtain ⟨hok1, hok2, hok3, hok4⟩ :=
    arithRegOkOverflow (op := .addOverflow destination resultCarry sourceLeft sourceRight)
      (Or.inl rfl) s1 s2 ms h
  obtain ⟨hlt1, _, hne31_1⟩ := regOk_of_asm hok1
  obtain ⟨hlt2, hav2, hne31_2⟩ := regOk_of_asm hok2
  obtain ⟨hlt3, hav3, hne31_3⟩ := regOk_of_asm hok3
  obtain ⟨hlt4, _, hne31_4⟩ := regOk_of_asm hok4
  have st := arm8Start (.inst (.arith (.addOverflow destination resultCarry sourceLeft
    sourceRight))) s1 s2 ms h
  have hasm : arm8Ast (.inst (.arith (.addOverflow destination resultCarry sourceLeft
      sourceRight))) =
      [.addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination,
       .conditionalSelect false true 7 31 31 sourceRight] := rfl
  have hb : bytesInMemoryHOL ms.pc
      ([.addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination,
        .conditionalSelect false true 7 31 31 sourceRight].flatMap encodeBytes) ms.mem
      s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hasm] at hb'
    exact hb'
  obtain ⟨hb1, hb2⟩ := (bytesInMemory_two ms.pc
    (.addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination)
    (.conditionalSelect false true 7 31 31 sourceRight) ms.mem s1.memDomain).1 hb
  let t : Nat → Arm8State := fun k =>
    match k with
    | 0 => ms
    | 1 => overflowAddT1 s1 ms destination resultCarry sourceLeft
    | _ => overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight
  have hnext1 : arm8Next ms = t 1 := by
    rw [arm8Next_addSubShiftedRegister ms s1.memDomain false true .lsl sourceLeft 0
      resultCarry destination hlt3 (by decide) hlt2 hlt1 hb1, execInsn_overflowAdd]
    show writeReg (writeFlags { ms with pc := ms.pc + 4 }
        (addFlags (readReg ms resultCarry) (readReg ms sourceLeft))) destination
        (readReg ms resultCarry + readReg ms sourceLeft) = _
    simp only [readReg, ite_eq_right hne31_2, ite_eq_right hne31_3]
    rw [msRegs st hlt2 hav2, msRegs st hlt3 hav3]
    rfl
  have ht1 : t 1 = overflowAddT1 s1 ms destination resultCarry sourceLeft := rfl
  have hnext2 : arm8Next (t 1) = t (1 + 1) := by
    have hb2' : bytesInMemoryHOL (t 1).pc
        (encodeBytes (.conditionalSelect false true 7 31 31 sourceRight)) (t 1).mem
        s1.memDomain := by
      rw [ht1, overflowAddT1, writeReg_pc, writeFlags_pc, writeReg_mem]
      exact hb2
    rw [arm8Next_conditionalSelect (t 1) s1.memDomain false true 7 31 31 sourceRight
      (by decide) (by decide) (by decide) hlt4 hb2', execInsn_conditionalSelect_v]
    rfl
  have hlen : (arm8Enc (.inst (.arith (.addOverflow destination resultCarry sourceLeft
      sourceRight)))).length = (1 + 1) * 4 := by
    rw [arm8Enc, hasm, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, encodeBytes_length, encodeBytes_length]
  have hupd : asmUpd (.inst (.arith (.addOverflow destination resultCarry sourceLeft
      sourceRight))) (s1.pc + BitVec.ofNat 64 ((1 + 1) * 4)) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 ((1 + 1) * 4) := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j =
      (if j = sourceRight then
        (if (s1.regs resultCarry + s1.regs sourceLeft).toInt ≠
          (s1.regs resultCarry).toInt + (s1.regs sourceLeft).toInt then 1 else 0)
       else if j = destination then s1.regs resultCarry + s1.regs sourceLeft
       else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_addOverflow_regs s1 destination resultCarry sourceLeft sourceRight j
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain
      (.addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination) _ hb1
      (encodeInsn_addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination)
      (decode_encode_addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination
        hlt3 (by decide) hlt2 hlt1) (by rfl)
  have hsafe1 : StepSafe s1.memDomain (t 1) := by
    have hb2' : bytesInMemoryHOL (t 1).pc
        (encodeBytes (.conditionalSelect false true 7 31 31 sourceRight)) (t 1).mem
        s1.memDomain := by
      rw [ht1, overflowAddT1, writeReg_pc, writeFlags_pc, writeReg_mem]
      exact hb2
    exact stepSafe_of_encode (t 1) s1.memDomain
      (.conditionalSelect false true 7 31 31 sourceRight) _ hb2'
      (encodeInsn_conditionalSelect false true 7 31 31 sourceRight)
      (decode_encode_conditionalSelect false true 7 31 31 sourceRight (by decide) (by decide)
        (by decide) hlt4) (by rfl)
  have hstate : ∀ k, 1 ≤ k → k ≤ 1 → arm8StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧
      (t k).pc = ms.pc + BitVec.ofNat 64 (k * 4) := by
    intro k h1 h2
    have hk1 : k = 1 := by omega
    subst hk1
    refine ⟨?_, ?_, ?_⟩
    · show arm8StateOk (overflowAddT1 s1 ms destination resultCarry sourceLeft) = true
      rw [overflowAddT1]
      refine arm8StateOk_set _ ?_ ?_
      · rw [writeReg_pc, writeFlags_pc,
          (alignedAddSub 2 ms.pc 4 (aligned_of_mod 4 (by decide))).1, st.aligned]
      · rw [writeReg_failed, writeFlags_failed]
        exact st.msFailed
    · intro x
      show (overflowAddT1 s1 ms destination resultCarry sourceLeft).mem x = ms.mem x
      rw [overflowAddT1, writeReg_mem, writeFlags_mem]
    · show (overflowAddT1 s1 ms destination resultCarry sourceLeft).pc
          = ms.pc + BitVec.ofNat 64 (1 * 4)
      rw [overflowAddT1, writeReg_pc, writeFlags_pc]
      bv_omega
  have hsafe : ∀ k, k ≤ 1 → StepSafe s1.memDomain (t k) := by
    intro k hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with h0 | h1
    · subst h0
      exact hsafe0
    · subst h1
      exact hsafe1
  have hq : targetStateRel arm8Target s2 (t (1 + 1)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show arm8StateOk (overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight)
        = true
      rw [overflowAddT2]
      refine arm8StateOk_set _ ?_ ?_
      · rw [writeReg_pc, overflowAddT1, writeReg_pc, writeFlags_pc,
          (alignedAddSub 2 (ms.pc + 4) 4 (aligned_of_mod 4 (by decide))).1,
          (alignedAddSub 2 ms.pc 4 (aligned_of_mod 4 (by decide))).1, st.aligned]
      · rw [writeReg_failed, overflowAddT1, writeReg_failed, writeFlags_failed]
        exact st.msFailed
    · show (overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight).pc = s2.pc
      rw [overflowAddT2, writeReg_pc, overflowAddT1, writeReg_pc, writeFlags_pc, st.pc, hs2pc]
      bv_omega
    · intro x hx
      show (overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight).mem x
        = s2.mem x
      rw [overflowAddT2, writeReg_mem, overflowAddT1, writeReg_mem, writeFlags_mem, hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro j hj
      show arm8Target.getReg
          (overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight) j = s2.regs j
      have hget : arm8Target.getReg
          (overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight) j
          = (overflowAddT2 s1 ms destination resultCarry sourceLeft sourceRight).regs j := rfl
      rw [hget]
      have hs := hs2regs j
      simp only [overflowAddT2, overflowAddT1, writeReg_regs _ hne31_4,
        writeReg_regs _ hne31_1, writeFlags_regs, writeReg_v, writeFlags_v]
      by_cases hju : j = sourceRight
      · rw [ite_eq_left hju] at hs ⊢
        rw [hs]
        simp only [addFlags_v, decide_eq_true_eq]
      · rw [ite_eq_right hju] at hs ⊢
        by_cases hjd : j = destination
        · rw [ite_eq_left hjd] at hs ⊢
          exact hs.symm
        · rw [ite_eq_right hjd] at hs ⊢
          rw [st.reg j hj]
          exact hs.symm
    · intro j hj
      simp only [arm8Target_config, arm8Config] at hj
      omega
  have hstep : ∀ k, k ≤ 1 → arm8Next (t k) = t (k + 1) := by
    intro k hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · subst hk0
      exact hnext1
    · subst hk1
      exact hnext2
  have ht0 : t 0 = ms := rfl
  exact arithRunCase _ s1 s2 ms 1 t ⟨h.1, h.2⟩ ht0 hlen hstep hstate hsafe hs2dom hq

/-- The `subOverflow` constructor of `encoder_correct arm8Target`. -/
theorem case_subOverflow (destination resultCarry sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1
        (.inst (.arith (.subOverflow destination resultCarry sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.subOverflow destination resultCarry sourceLeft sourceRight)))
      s1 s2 ms := by
  obtain ⟨hok1, hok2, hok3, hok4⟩ :=
    arithRegOkOverflow (op := .subOverflow destination resultCarry sourceLeft sourceRight)
      (Or.inr rfl) s1 s2 ms h
  obtain ⟨hlt1, _, hne31_1⟩ := regOk_of_asm hok1
  obtain ⟨hlt2, hav2, hne31_2⟩ := regOk_of_asm hok2
  obtain ⟨hlt3, hav3, hne31_3⟩ := regOk_of_asm hok3
  obtain ⟨hlt4, _, hne31_4⟩ := regOk_of_asm hok4
  have st := arm8Start (.inst (.arith (.subOverflow destination resultCarry sourceLeft
    sourceRight))) s1 s2 ms h
  have hasm : arm8Ast (.inst (.arith (.subOverflow destination resultCarry sourceLeft
      sourceRight))) =
      [.addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination,
       .conditionalSelect false true 7 31 31 sourceRight] := rfl
  have hb : bytesInMemoryHOL ms.pc
      ([.addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination,
        .conditionalSelect false true 7 31 31 sourceRight].flatMap encodeBytes) ms.mem
      s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hasm] at hb'
    exact hb'
  obtain ⟨hb1, hb2⟩ := (bytesInMemory_two ms.pc
    (.addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination)
    (.conditionalSelect false true 7 31 31 sourceRight) ms.mem s1.memDomain).1 hb
  let t : Nat → Arm8State := fun k =>
    match k with
    | 0 => ms
    | 1 => overflowSubT1 s1 ms destination resultCarry sourceLeft
    | _ => overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight
  have hnext1 : arm8Next ms = t 1 := by
    rw [arm8Next_addSubShiftedRegister ms s1.memDomain true true .lsl sourceLeft 0
      resultCarry destination hlt3 (by decide) hlt2 hlt1 hb1, execInsn_overflowSub]
    show writeReg (writeFlags { ms with pc := ms.pc + 4 }
        (subFlags (readReg ms resultCarry) (readReg ms sourceLeft))) destination
        (readReg ms resultCarry - readReg ms sourceLeft) = _
    simp only [readReg, ite_eq_right hne31_2, ite_eq_right hne31_3]
    rw [msRegs st hlt2 hav2, msRegs st hlt3 hav3]
    rfl
  have ht1 : t 1 = overflowSubT1 s1 ms destination resultCarry sourceLeft := rfl
  have hnext2 : arm8Next (t 1) = t (1 + 1) := by
    have hb2' : bytesInMemoryHOL (t 1).pc
        (encodeBytes (.conditionalSelect false true 7 31 31 sourceRight)) (t 1).mem
        s1.memDomain := by
      rw [ht1, overflowSubT1, writeReg_pc, writeFlags_pc, writeReg_mem]
      exact hb2
    rw [arm8Next_conditionalSelect (t 1) s1.memDomain false true 7 31 31 sourceRight
      (by decide) (by decide) (by decide) hlt4 hb2', execInsn_conditionalSelect_v]
    rfl
  have hlen : (arm8Enc (.inst (.arith (.subOverflow destination resultCarry sourceLeft
      sourceRight)))).length = (1 + 1) * 4 := by
    rw [arm8Enc, hasm, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, encodeBytes_length, encodeBytes_length]
  have hupd : asmUpd (.inst (.arith (.subOverflow destination resultCarry sourceLeft
      sourceRight))) (s1.pc + BitVec.ofNat 64 ((1 + 1) * 4)) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 ((1 + 1) * 4) := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j =
      (if j = sourceRight then
        (if (s1.regs resultCarry - s1.regs sourceLeft).toInt ≠
          (s1.regs resultCarry).toInt - (s1.regs sourceLeft).toInt then 1 else 0)
       else if j = destination then s1.regs resultCarry - s1.regs sourceLeft
       else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_subOverflow_regs s1 destination resultCarry sourceLeft sourceRight j
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain
      (.addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination) _ hb1
      (encodeInsn_addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination)
      (decode_encode_addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination
        hlt3 (by decide) hlt2 hlt1) (by rfl)
  have hsafe1 : StepSafe s1.memDomain (t 1) := by
    have hb2' : bytesInMemoryHOL (t 1).pc
        (encodeBytes (.conditionalSelect false true 7 31 31 sourceRight)) (t 1).mem
        s1.memDomain := by
      rw [ht1, overflowSubT1, writeReg_pc, writeFlags_pc, writeReg_mem]
      exact hb2
    exact stepSafe_of_encode (t 1) s1.memDomain
      (.conditionalSelect false true 7 31 31 sourceRight) _ hb2'
      (encodeInsn_conditionalSelect false true 7 31 31 sourceRight)
      (decode_encode_conditionalSelect false true 7 31 31 sourceRight (by decide) (by decide)
        (by decide) hlt4) (by rfl)
  have hstate : ∀ k, 1 ≤ k → k ≤ 1 → arm8StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧
      (t k).pc = ms.pc + BitVec.ofNat 64 (k * 4) := by
    intro k h1 h2
    have hk1 : k = 1 := by omega
    subst hk1
    refine ⟨?_, ?_, ?_⟩
    · show arm8StateOk (overflowSubT1 s1 ms destination resultCarry sourceLeft) = true
      rw [overflowSubT1]
      refine arm8StateOk_set _ ?_ ?_
      · rw [writeReg_pc, writeFlags_pc,
          (alignedAddSub 2 ms.pc 4 (aligned_of_mod 4 (by decide))).1, st.aligned]
      · rw [writeReg_failed, writeFlags_failed]
        exact st.msFailed
    · intro x
      show (overflowSubT1 s1 ms destination resultCarry sourceLeft).mem x = ms.mem x
      rw [overflowSubT1, writeReg_mem, writeFlags_mem]
    · show (overflowSubT1 s1 ms destination resultCarry sourceLeft).pc
          = ms.pc + BitVec.ofNat 64 (1 * 4)
      rw [overflowSubT1, writeReg_pc, writeFlags_pc]
      bv_omega
  have hsafe : ∀ k, k ≤ 1 → StepSafe s1.memDomain (t k) := by
    intro k hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with h0 | h1
    · subst h0
      exact hsafe0
    · subst h1
      exact hsafe1
  have hq : targetStateRel arm8Target s2 (t (1 + 1)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show arm8StateOk (overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight)
        = true
      rw [overflowSubT2]
      refine arm8StateOk_set _ ?_ ?_
      · rw [writeReg_pc, overflowSubT1, writeReg_pc, writeFlags_pc,
          (alignedAddSub 2 (ms.pc + 4) 4 (aligned_of_mod 4 (by decide))).1,
          (alignedAddSub 2 ms.pc 4 (aligned_of_mod 4 (by decide))).1, st.aligned]
      · rw [writeReg_failed, overflowSubT1, writeReg_failed, writeFlags_failed]
        exact st.msFailed
    · show (overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight).pc = s2.pc
      rw [overflowSubT2, writeReg_pc, overflowSubT1, writeReg_pc, writeFlags_pc, st.pc, hs2pc]
      bv_omega
    · intro x hx
      show (overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight).mem x
        = s2.mem x
      rw [overflowSubT2, writeReg_mem, overflowSubT1, writeReg_mem, writeFlags_mem, hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro j hj
      show arm8Target.getReg
          (overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight) j = s2.regs j
      have hget : arm8Target.getReg
          (overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight) j
          = (overflowSubT2 s1 ms destination resultCarry sourceLeft sourceRight).regs j := rfl
      rw [hget]
      have hs := hs2regs j
      simp only [overflowSubT2, overflowSubT1, writeReg_regs _ hne31_4,
        writeReg_regs _ hne31_1, writeFlags_regs, writeReg_v, writeFlags_v]
      by_cases hju : j = sourceRight
      · rw [ite_eq_left hju] at hs ⊢
        rw [hs]
        simp only [subFlags_v, decide_eq_true_eq]
      · rw [ite_eq_right hju] at hs ⊢
        by_cases hjd : j = destination
        · rw [ite_eq_left hjd] at hs ⊢
          exact hs.symm
        · rw [ite_eq_right hjd] at hs ⊢
          rw [st.reg j hj]
          exact hs.symm
    · intro j hj
      simp only [arm8Target_config, arm8Config] at hj
      omega
  have hstep : ∀ k, k ≤ 1 → arm8Next (t k) = t (k + 1) := by
    intro k hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · subst hk0
      exact hnext1
    · subst hk1
      exact hnext2
  have ht0 : t 0 = ms := rfl
  exact arithRunCase _ s1 s2 ms 1 t ⟨h.1, h.2⟩ ht0 hlen hstep hstate hsafe hs2dom hq

/-! ## The `addCarry` case -/

/-- A sum below `2 ^ 65` is its own residue modulo `2 ^ 64` exactly when it fits one
machine word. -/
theorem mod_ne_self_iff (S : Nat) (hS : S < 2 ^ 65) :
    (S % 2 ^ 64 ≠ S) ↔ 2 ^ 64 ≤ S := by
  constructor
  · intro h
    by_contra hlt
    exact h (Nat.mod_eq_of_lt (Nat.not_le.mp hlt))
  · intro hge
    have h65 : (2 : Nat) ^ 65 = 2 ^ 64 + 2 ^ 64 := by norm_num
    have hlt : S - 2 ^ 64 < 2 ^ 64 := by omega
    have hsplit : S = 2 ^ 64 + (S - 2 ^ 64) := (Nat.add_sub_cancel' hge).symm
    rw [hsplit, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

/-- Two `if`s with the same proposition are the same, whatever their `Decidable`
instances. -/
theorem ite_of_iff {α : Sort u} {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (a b : α) :
    (if p then a else b) = (if q then a else b) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun hq => hp (h.mpr hq))]

/-- Two `decide`s of the same proposition agree, whatever their `Decidable` instances. -/
theorem decide_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

/-- Executing the carry test `ADDS XZR, ry, #0`. -/
theorem execInsn_carryTest (s : Arm8State) (rn : Nat) :
    execInsn s (.addSubImmediate true true 0 rn 31) =
      writeFlags s (addWithCarry (readReg s rn) (~~~(0 : BitVec 64)) true).2 := by
  simp only [execInsn, ↓reduceIte, writeReg_zero_reg]

/-- The carry test `ADDS XZR, ry, #0` leaves `ry` unchanged. -/
theorem addCarry_test_val (x : BitVec 64) :
    (addWithCarry x (~~~(0 : BitVec 64)) true).1 = x := by
  rw [addWithCarry_val]
  simp only [↓reduceIte]
  rw [arith_add_not_add_one x 0]
  bv_omega

/-- The `Z` flag of the carry test. -/
theorem addCarry_test_z (x : BitVec 64) :
    (addWithCarry x (~~~(0 : BitVec 64)) true).2.2.1 = decide (x = 0) := by
  rw [addWithCarry_flags, addCarry_test_val]

/-- The `C` flag left by the conditional compare of the carry-in. -/
theorem addCarry_c_test (sr rc : BitVec 64) :
    (if decide (sr = 0) then (addWithCarry rc (BitVec.ofNat 64 0) false).2
      else (false, false, true, false)).2.2.1 = decide (sr ≠ 0) := by
  by_cases h : sr = 0
  · subst h
    simp [addWithCarry_addFlags, addFlags]
  · have hd : decide (sr = 0) = false := decide_eq_false_iff_not.mpr h
    rw [hd]
    have hne : decide (sr ≠ 0) = true := decide_eq_true_iff.mpr h
    rw [hne]
    simp

/-- Executing the conditional compare of the carry-in. -/
theorem execInsn_carryCcmp (s : Arm8State) (rc : Nat) :
    execInsn s (.conditionalCompareImmediate false (BitVec.ofNat 64 0) 0
      (false, false, true, false) rc) =
      writeFlags s (if s.z then (addWithCarry (readReg s rc) (BitVec.ofNat 64 0) false).2
        else (false, false, true, false)) := by
  simp only [execInsn, conditionHolds, Bool.false_eq_true, ↓reduceIte]

/-- Executing the flag-setting carry addition. -/
theorem execInsn_carryAdd (s : Arm8State) (sl rc d : Nat) :
    execInsn s (.addSubCarry false true sl rc d) =
      writeReg (writeFlags s (addWithCarry (readReg s rc) (readReg s sl) s.c).2) d
        (addWithCarry (readReg s rc) (readReg s sl) s.c).1 := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]

/-- Executing the zeroing move of the carry-out register. -/
theorem execInsn_carryZero (s : Arm8State) (sr : Nat) :
    execInsn s (.moveWide .z 0 0 sr) = writeReg s sr 0 := by
  simp [execInsn]

/-- Executing the carry-out `ADC`. -/
theorem execInsn_carryOut (s : Arm8State) (sr : Nat) (h0 : readReg s sr = 0) :
    execInsn s (.addSubCarry false false 31 sr sr) = writeReg s sr (if s.c then 1 else 0) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte, addWithCarry_val]
  have h31 : readReg s 31 = (0 : BitVec 64) := by simp [readReg]
  rw [h0, h31]
  simp

/-- The value a carry addition produces. -/
theorem addCarry_sum_val (rc sl : BitVec 64) (cin : Bool) :
    (addWithCarry rc sl cin).1 =
      BitVec.ofNat 64 (rc.toNat + sl.toNat + (if cin then 1 else 0)) := by
  rw [addWithCarry_val]
  cases cin with
  | false => simpa using (arith_ofNat64_add_toNat rc sl).symm
  | true => simpa using (arith_ofNat64_add_one rc sl).symm

/-- The `C` flag of a carry addition is its `Nat` sum exceeding one word. -/
theorem addWithCarry_carryOut (x y : BitVec 64) (cin : Bool) :
    (addWithCarry x y cin).2.2.2.1 =
      decide (2 ^ 64 ≤ x.toNat + y.toNat + (if cin then 1 else 0)) := by
  have hk : (if cin then 1 else 0) ≤ 1 := by cases cin <;> simp
  have hS : x.toNat + y.toNat + (if cin then 1 else 0) < 2 ^ 65 := by
    have hx := x.isLt
    have hy := y.isLt
    omega
  rw [addWithCarry_flags, addCarry_sum_val]
  simp only [BitVec.toNat_ofNat]
  rw [decide_eq_decide]
  exact mod_ne_self_iff _ hS

/-- The `Nat` sum an `addCarry` computes. -/
def carryNat (s1 : AsmState 64) (sr rc sl : Nat) : Nat :=
  (s1.regs rc).toNat + (s1.regs sl).toNat + (if s1.regs sr = 0 then 0 else 1)

/-- The carry-in bit as a `Nat`. -/
theorem ite_carry_nat (sr : BitVec 64) :
    (if decide (sr ≠ 0) then (1 : Nat) else 0) = if sr = 0 then 0 else 1 := by
  by_cases h : sr = 0 <;> simp [h]

/-- The state after running the instruction at the program counter. -/
def pcNext (s : Arm8State) : Arm8State := { s with pc := s.pc + 4 }

theorem pcNext_pc (s : Arm8State) : (pcNext s).pc = s.pc + 4 := rfl

theorem pcNext_regs (s : Arm8State) : (pcNext s).regs = s.regs := rfl

theorem pcNext_mem (s : Arm8State) : (pcNext s).mem = s.mem := rfl

theorem pcNext_failed (s : Arm8State) : (pcNext s).failed = s.failed := rfl

theorem pcNext_z (s : Arm8State) : (pcNext s).z = s.z := rfl

theorem pcNext_c (s : Arm8State) : (pcNext s).c = s.c := rfl

/-- Reading a register of the advanced state. -/
theorem readReg_pcNext_field (s : Arm8State) (r : Nat) (h : r ≠ 31) :
    readReg (pcNext s) r = s.regs r := by
  rw [readReg, ite_eq_right h, pcNext_regs]

/-- The state after the carry test of an `addCarry`. -/
def carryT1 (s1 : AsmState 64) (ms : Arm8State) (sr : Nat) : Arm8State :=
  writeFlags (pcNext ms) (addWithCarry (s1.regs sr) (~~~(0 : BitVec 64)) true).2

/-- The state after the conditional compare of an `addCarry`. -/
def carryT2 (s1 : AsmState 64) (ms : Arm8State) (sr rc : Nat) : Arm8State :=
  writeFlags (pcNext (carryT1 s1 ms sr))
    (if decide (s1.regs sr = 0) then (addWithCarry (s1.regs rc) (BitVec.ofNat 64 0) false).2
     else (false, false, true, false))

/-- The state after the flag-setting carry addition of an `addCarry`. -/
def carryT3 (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) : Arm8State :=
  writeReg (writeFlags (pcNext (carryT2 s1 ms sr rc))
    (addWithCarry (s1.regs rc) (s1.regs sl) (carryT2 s1 ms sr rc).c).2) d
    (BitVec.ofNat 64 (carryNat s1 sr rc sl))

/-- The state after zeroing the carry-out register of an `addCarry`. -/
def carryT4 (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) : Arm8State :=
  writeReg (pcNext (carryT3 s1 ms sr rc sl d)) sr 0

/-- The final state of an `addCarry`. -/
def carryT5 (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) : Arm8State :=
  writeReg (pcNext (carryT4 s1 ms sr rc sl d)) sr
    (if 2 ^ 64 ≤ carryNat s1 sr rc sl then 1 else 0)

/-- The `Z` flag of the carry test of an `addCarry`. -/
theorem carryT1_z (s1 : AsmState 64) (ms : Arm8State) (sr : Nat) :
    (carryT1 s1 ms sr).z = decide (s1.regs sr = 0) := by
  rw [carryT1, writeFlags_z]
  exact addCarry_test_z (s1.regs sr)

/-- The `C` flag after the conditional compare of an `addCarry`. -/
theorem carryT2_c (s1 : AsmState 64) (ms : Arm8State) (sr rc : Nat) :
    (carryT2 s1 ms sr rc).c = decide (s1.regs sr ≠ 0) := by
  rw [carryT2, writeFlags_c]
  exact addCarry_c_test (s1.regs sr) (s1.regs rc)

/-- The `C` flag of the carry-out addition of an `addCarry`. -/
theorem carryT3_c (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT3 s1 ms sr rc sl d).c = decide (2 ^ 64 ≤ carryNat s1 sr rc sl) := by
  rw [carryT3, writeReg_c, writeFlags_c, carryT2_c, addWithCarry_carryOut, ite_carry_nat]
  exact decide_of_iff Iff.rfl

/-- The `C` flag of the zeroing state of an `addCarry`. -/
theorem carryT4_c (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT4 s1 ms sr rc sl d).c = decide (2 ^ 64 ≤ carryNat s1 sr rc sl) := by
  rw [carryT4, writeReg_c, pcNext_c]
  exact carryT3_c s1 ms sr rc sl d

/-- The program counter of the carry test state. -/
theorem carryT1_pc (s1 : AsmState 64) (ms : Arm8State) (sr : Nat) :
    (carryT1 s1 ms sr).pc = ms.pc + 4 := by
  rw [carryT1, writeFlags_pc, pcNext_pc]

/-- The program counter of the carry-in state. -/
theorem carryT2_pc (s1 : AsmState 64) (ms : Arm8State) (sr rc : Nat) :
    (carryT2 s1 ms sr rc).pc = ms.pc + 4 + 4 := by
  rw [carryT2, writeFlags_pc, pcNext_pc, carryT1_pc]

/-- The program counter of the carry-addition state. -/
theorem carryT3_pc (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT3 s1 ms sr rc sl d).pc = ms.pc + 4 + 4 + 4 := by
  rw [carryT3, writeReg_pc, writeFlags_pc, pcNext_pc, carryT2_pc]

/-- The program counter of the zeroing state. -/
theorem carryT4_pc (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT4 s1 ms sr rc sl d).pc = ms.pc + 4 + 4 + 4 + 4 := by
  rw [carryT4, writeReg_pc, pcNext_pc, carryT3_pc]

/-- The program counter of the final state. -/
theorem carryT5_pc (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT5 s1 ms sr rc sl d).pc = ms.pc + 4 + 4 + 4 + 4 + 4 := by
  rw [carryT5, writeReg_pc, pcNext_pc, carryT4_pc]

/-- The memory of the carry test state. -/
theorem carryT1_mem (s1 : AsmState 64) (ms : Arm8State) (sr : Nat) :
    (carryT1 s1 ms sr).mem = ms.mem := by
  rw [carryT1, writeFlags_mem, pcNext_mem]

/-- The memory of the carry-in state. -/
theorem carryT2_mem (s1 : AsmState 64) (ms : Arm8State) (sr rc : Nat) :
    (carryT2 s1 ms sr rc).mem = ms.mem := by
  rw [carryT2, writeFlags_mem, pcNext_mem, carryT1_mem]

/-- The memory of the carry-addition state. -/
theorem carryT3_mem (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT3 s1 ms sr rc sl d).mem = ms.mem := by
  rw [carryT3, writeReg_mem, writeFlags_mem, pcNext_mem, carryT2_mem]

/-- The memory of the zeroing state. -/
theorem carryT4_mem (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT4 s1 ms sr rc sl d).mem = ms.mem := by
  rw [carryT4, writeReg_mem, pcNext_mem, carryT3_mem]

/-- The memory of the final state. -/
theorem carryT5_mem (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT5 s1 ms sr rc sl d).mem = ms.mem := by
  rw [carryT5, writeReg_mem, pcNext_mem, carryT4_mem]

/-- The failure flag of the carry test state. -/
theorem carryT1_failed (s1 : AsmState 64) (ms : Arm8State) (sr : Nat) :
    (carryT1 s1 ms sr).failed = ms.failed := by
  rw [carryT1, writeFlags_failed, pcNext_failed]

/-- The failure flag of the carry-in state. -/
theorem carryT2_failed (s1 : AsmState 64) (ms : Arm8State) (sr rc : Nat) :
    (carryT2 s1 ms sr rc).failed = ms.failed := by
  rw [carryT2, writeFlags_failed, pcNext_failed, carryT1_failed]

/-- The failure flag of the carry-addition state. -/
theorem carryT3_failed (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT3 s1 ms sr rc sl d).failed = ms.failed := by
  rw [carryT3, writeReg_failed, writeFlags_failed, pcNext_failed, carryT2_failed]

/-- The failure flag of the zeroing state. -/
theorem carryT4_failed (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT4 s1 ms sr rc sl d).failed = ms.failed := by
  rw [carryT4, writeReg_failed, pcNext_failed, carryT3_failed]

/-- The failure flag of the final state. -/
theorem carryT5_failed (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) :
    (carryT5 s1 ms sr rc sl d).failed = ms.failed := by
  rw [carryT5, writeReg_failed, pcNext_failed, carryT4_failed]

/-- The registers of the carry test state. -/
theorem carryT1_regs (s1 : AsmState 64) (ms : Arm8State) (sr : Nat) :
    (carryT1 s1 ms sr).regs = ms.regs := by
  rw [carryT1, writeFlags_regs, pcNext_regs]

/-- The registers of the carry-in state. -/
theorem carryT2_regs (s1 : AsmState 64) (ms : Arm8State) (sr rc : Nat) :
    (carryT2 s1 ms sr rc).regs = ms.regs := by
  rw [carryT2, writeFlags_regs, pcNext_regs, carryT1_regs]

/-- The registers of the carry-addition state. -/
theorem carryT3_regs (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) (hd : d ≠ 31) :
    ∀ j, (carryT3 s1 ms sr rc sl d).regs j =
      if j = d then BitVec.ofNat 64 (carryNat s1 sr rc sl) else ms.regs j := by
  intro j
  rw [carryT3, writeReg_regs _ hd]
  by_cases hjd : j = d
  · simp [hjd]
  · simp [hjd, writeFlags_regs, pcNext_regs, carryT2_regs]

/-- The registers of the zeroing state. -/
theorem carryT4_regs (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) (hsr : sr ≠ 31)
    (hd : d ≠ 31) :
    ∀ j, (carryT4 s1 ms sr rc sl d).regs j =
      if j = sr then 0 else if j = d then BitVec.ofNat 64 (carryNat s1 sr rc sl) else ms.regs j := by
  intro j
  rw [carryT4, writeReg_regs _ hsr]
  by_cases hjs : j = sr
  · simp [hjs]
  · simp [hjs, pcNext_regs, carryT3_regs _ _ _ _ _ _ hd]

/-- The registers of the final state. -/
theorem carryT5_regs (s1 : AsmState 64) (ms : Arm8State) (sr rc sl d : Nat) (hsr : sr ≠ 31)
    (hd : d ≠ 31) :
    ∀ j, (carryT5 s1 ms sr rc sl d).regs j =
      if j = sr then (if 2 ^ 64 ≤ carryNat s1 sr rc sl then 1 else 0)
      else if j = d then BitVec.ofNat 64 (carryNat s1 sr rc sl) else ms.regs j := by
  intro j
  rw [carryT5, writeReg_regs _ hsr]
  by_cases hjs : j = sr
  · simp [hjs]
  · simp [hjs, pcNext_regs, carryT4_regs _ _ _ _ _ _ hsr hd]

/-- The register side conditions of an `addCarry`. -/
theorem arithRegOkCarry {r1 r2 r3 r4 : Nat} (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.addCarry r1 r2 r3 r4))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    asmRegOkExact r1 arm8Config = true ∧ asmRegOkExact r2 arm8Config = true ∧
      asmRegOkExact r3 arm8Config = true ∧ asmRegOkExact r4 arm8Config = true := by
  have hb := (arm8Start _ s1 s2 ms h).asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8_twoRegArith, arm8_isa_mips,
    arm8_isa_riscv, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_eq_true,
    and_assoc, true_and, and_true] at hb
  exact hb

/-- The register update of an `addCarry`. -/
theorem arithUpd_addCarry_regs (s : AsmState 64) (r1 r2 r3 r4 : Nat) :
    ∀ j, (arithUpd (.addCarry r1 r2 r3 r4) s).regs j =
      (if j = r4 then
        (if 2 ^ 64 ≤ (s.regs r2).toNat + (s.regs r3).toNat +
          (if s.regs r4 = 0 then 0 else 1) then 1 else 0)
       else if j = r1 then BitVec.ofNat 64 ((s.regs r2).toNat + (s.regs r3).toNat +
          (if s.regs r4 = 0 then 0 else 1)) else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg]
  by_cases h4 : j = r4
  · simp only [ite_eq_left h4]
    exact ite_of_iff Iff.rfl _ _
  · simp only [ite_eq_right h4]
    exact ite_of_iff Iff.rfl _ _

/-- The `addCarry` constructor of `encoder_correct arm8Target`. -/
theorem case_addCarry (destination resultCarry sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1
        (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight)))
      s1 s2 ms := by
  obtain ⟨hok1, hok2, hok3, hok4⟩ :=
    arithRegOkCarry (r1 := destination) (r2 := resultCarry) (r3 := sourceLeft)
      (r4 := sourceRight) s1 s2 ms h
  obtain ⟨hlt1, _, hne31_1⟩ := regOk_of_asm hok1
  obtain ⟨hlt2, hav2, hne31_2⟩ := regOk_of_asm hok2
  obtain ⟨hlt3, hav3, hne31_3⟩ := regOk_of_asm hok3
  obtain ⟨hlt4, hav4, hne31_4⟩ := regOk_of_asm hok4
  have st := arm8Start (.inst (.arith (.addCarry destination resultCarry sourceLeft
    sourceRight))) s1 s2 ms h
  have hasm : arm8Ast (.inst (.arith (.addCarry destination resultCarry sourceLeft
      sourceRight))) =
      [.addSubImmediate true true 0 sourceRight 31,
       .conditionalCompareImmediate false 0 0 (false, false, true, false) resultCarry,
       .addSubCarry false true sourceLeft resultCarry destination,
       .moveWide .z 0 0 sourceRight,
       .addSubCarry false false 31 sourceRight sourceRight] := rfl
  have hb : bytesInMemoryHOL ms.pc
      ([.addSubImmediate true true 0 sourceRight 31,
        .conditionalCompareImmediate false 0 0 (false, false, true, false) resultCarry,
        .addSubCarry false true sourceLeft resultCarry destination,
        .moveWide .z 0 0 sourceRight,
        .addSubCarry false false 31 sourceRight sourceRight].flatMap encodeBytes) ms.mem
      s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hasm] at hb'
    exact hb'
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := (bytesInMemory_five ms.pc
    (.addSubImmediate true true 0 sourceRight 31)
    (.conditionalCompareImmediate false 0 0 (false, false, true, false) resultCarry)
    (.addSubCarry false true sourceLeft resultCarry destination)
    (.moveWide .z 0 0 sourceRight)
    (.addSubCarry false false 31 sourceRight sourceRight) ms.mem s1.memDomain).1 hb
  let t : Nat → Arm8State := fun k =>
    match k with
    | 0 => ms
    | 1 => carryT1 s1 ms sourceRight
    | 2 => carryT2 s1 ms sourceRight resultCarry
    | 3 => carryT3 s1 ms sourceRight resultCarry sourceLeft destination
    | 4 => carryT4 s1 ms sourceRight resultCarry sourceLeft destination
    | _ => carryT5 s1 ms sourceRight resultCarry sourceLeft destination
  have hstep1 : arm8Next ms = carryT1 s1 ms sourceRight := by
    rw [arm8Next_addSubImmediate ms s1.memDomain true true 0 sourceRight 31 (by decide) hlt4
      (by decide) hb1, execInsn_carryTest]
    rw [show { ms with pc := ms.pc + 4 } = pcNext ms from rfl,
      readReg_pcNext_field ms sourceRight hne31_4, msRegs st hlt4 hav4]
    rfl
  have hstep2 : arm8Next (carryT1 s1 ms sourceRight) = carryT2 s1 ms sourceRight resultCarry := by
    have hb2' : bytesInMemoryHOL (carryT1 s1 ms sourceRight).pc
        (encodeBytes (.conditionalCompareImmediate false 0 0 (false, false, true, false)
          resultCarry)) (carryT1 s1 ms sourceRight).mem s1.memDomain := by
      rw [carryT1_pc, carryT1_mem]
      exact hb2
    rw [arm8Next_conditionalCompareImmediate (carryT1 s1 ms sourceRight) s1.memDomain false 0 0
      resultCarry false false true false (by decide) (by decide) hlt2 hb2', execInsn_carryCcmp]
    rw [show { carryT1 s1 ms sourceRight with pc := (carryT1 s1 ms sourceRight).pc + 4 }
        = pcNext (carryT1 s1 ms sourceRight) from rfl,
      pcNext_z (carryT1 s1 ms sourceRight), carryT1_z,
      readReg_pcNext_field (carryT1 s1 ms sourceRight) resultCarry hne31_2,
      carryT1_regs, msRegs st hlt2 hav2]
    rfl
  have hstep3 : arm8Next (carryT2 s1 ms sourceRight resultCarry) =
      carryT3 s1 ms sourceRight resultCarry sourceLeft destination := by
    have hb3' : bytesInMemoryHOL (carryT2 s1 ms sourceRight resultCarry).pc
        (encodeBytes (.addSubCarry false true sourceLeft resultCarry destination))
        (carryT2 s1 ms sourceRight resultCarry).mem s1.memDomain := by
      rw [carryT2_pc, carryT2_mem]
      exact hb3
    rw [arm8Next_addSubCarry (carryT2 s1 ms sourceRight resultCarry) s1.memDomain false true
      sourceLeft resultCarry destination hlt3 hlt2 hlt1 hb3', execInsn_carryAdd]
    rw [carryT3, show { carryT2 s1 ms sourceRight resultCarry with
          pc := (carryT2 s1 ms sourceRight resultCarry).pc + 4 }
        = pcNext (carryT2 s1 ms sourceRight resultCarry) from rfl,
      readReg_pcNext_field (carryT2 s1 ms sourceRight resultCarry) resultCarry hne31_2,
      readReg_pcNext_field (carryT2 s1 ms sourceRight resultCarry) sourceLeft hne31_3,
      pcNext_c (carryT2 s1 ms sourceRight resultCarry), carryT2_regs,
      msRegs st hlt2 hav2, msRegs st hlt3 hav3, addCarry_sum_val, carryT2_c,
      ite_carry_nat]
    simp only [carryNat]
  have hstep4 : arm8Next (carryT3 s1 ms sourceRight resultCarry sourceLeft destination) =
      carryT4 s1 ms sourceRight resultCarry sourceLeft destination := by
    have hb4' : bytesInMemoryHOL
        (carryT3 s1 ms sourceRight resultCarry sourceLeft destination).pc
        (encodeBytes (.moveWide .z 0 0 sourceRight))
        (carryT3 s1 ms sourceRight resultCarry sourceLeft destination).mem s1.memDomain := by
      rw [carryT3_pc, carryT3_mem]
      exact hb4
    rw [arm8Next_moveWide (carryT3 s1 ms sourceRight resultCarry sourceLeft destination)
      s1.memDomain .z 0 0 sourceRight (by decide) (by decide) hlt4 hb4',
      execInsn_carryZero,
      show { carryT3 s1 ms sourceRight resultCarry sourceLeft destination with
          pc := (carryT3 s1 ms sourceRight resultCarry sourceLeft destination).pc + 4 }
        = pcNext (carryT3 s1 ms sourceRight resultCarry sourceLeft destination) from rfl]
    rfl
  have hstep5 : arm8Next (carryT4 s1 ms sourceRight resultCarry sourceLeft destination) =
      carryT5 s1 ms sourceRight resultCarry sourceLeft destination := by
    have hz : readReg (pcNext (carryT4 s1 ms sourceRight resultCarry sourceLeft destination))
        sourceRight = 0 := by
      rw [readReg_pcNext_field _ sourceRight hne31_4,
        carryT4_regs _ _ _ _ _ _ hne31_4 hne31_1, ite_eq_left rfl]
    have hb5' : bytesInMemoryHOL
        (carryT4 s1 ms sourceRight resultCarry sourceLeft destination).pc
        (encodeBytes (.addSubCarry false false 31 sourceRight sourceRight))
        (carryT4 s1 ms sourceRight resultCarry sourceLeft destination).mem s1.memDomain := by
      rw [carryT4_pc, carryT4_mem]
      exact hb5
    rw [arm8Next_addSubCarry (carryT4 s1 ms sourceRight resultCarry sourceLeft destination)
      s1.memDomain false false 31 sourceRight sourceRight (by decide) hlt4 hlt4 hb5',
      show { carryT4 s1 ms sourceRight resultCarry sourceLeft destination with
          pc := (carryT4 s1 ms sourceRight resultCarry sourceLeft destination).pc + 4 }
        = pcNext (carryT4 s1 ms sourceRight resultCarry sourceLeft destination) from rfl,
      execInsn_carryOut _ _ hz, pcNext_c (carryT4 s1 ms sourceRight resultCarry sourceLeft
        destination), carryT4_c, ite_decide_eq]
    rfl
  have hlen : (arm8Enc (.inst (.arith (.addCarry destination resultCarry sourceLeft
      sourceRight)))).length = (4 + 1) * 4 := by
    rw [arm8Enc, hasm, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, List.length_append, List.length_append, List.length_append,
      encodeBytes_length, encodeBytes_length, encodeBytes_length, encodeBytes_length,
      encodeBytes_length]
  have hupd : asmUpd (.inst (.arith (.addCarry destination resultCarry sourceLeft
      sourceRight))) (s1.pc + BitVec.ofNat 64 ((4 + 1) * 4)) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 ((4 + 1) * 4) := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j =
      (if j = sourceRight then
        (if 2 ^ 64 ≤ carryNat s1 sourceRight resultCarry sourceLeft then 1 else 0)
       else if j = destination then
          BitVec.ofNat 64 (carryNat s1 sourceRight resultCarry sourceLeft)
       else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_addCarry_regs s1 destination resultCarry sourceLeft sourceRight j
  have hal1 : holAligned 2 (ms.pc + 4) = true := by
    rw [(alignedAddSub 2 ms.pc 4 (aligned_of_mod 4 (by decide))).1, st.aligned]
  have hal2 : holAligned 2 (ms.pc + 4 + 4) = true := by
    rw [(alignedAddSub 2 (ms.pc + 4) 4 (aligned_of_mod 4 (by decide))).1, hal1]
  have hal3 : holAligned 2 (ms.pc + 4 + 4 + 4) = true := by
    rw [(alignedAddSub 2 (ms.pc + 4 + 4) 4 (aligned_of_mod 4 (by decide))).1, hal2]
  have hal4 : holAligned 2 (ms.pc + 4 + 4 + 4 + 4) = true := by
    rw [(alignedAddSub 2 (ms.pc + 4 + 4 + 4) 4 (aligned_of_mod 4 (by decide))).1, hal3]
  have hal5 : holAligned 2 (ms.pc + 4 + 4 + 4 + 4 + 4) = true := by
    rw [(alignedAddSub 2 (ms.pc + 4 + 4 + 4 + 4) 4 (aligned_of_mod 4 (by decide))).1, hal4]
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain _ _ hb1
      (encodeInsn_addSubImmediate true true 0 sourceRight 31 (by decide))
      (decode_encode_addSubImmediate true true 0 sourceRight 31 (by decide) hlt4 (by decide))
      (by rfl)
  have hsafe1 : StepSafe s1.memDomain (t 1) := by
    have hb2' : bytesInMemoryHOL (carryT1 s1 ms sourceRight).pc
        (encodeBytes (.conditionalCompareImmediate false 0 0 (false, false, true, false)
          resultCarry)) (carryT1 s1 ms sourceRight).mem s1.memDomain := by
      rw [carryT1_pc, carryT1_mem]
      exact hb2
    exact stepSafe_of_encode (carryT1 s1 ms sourceRight) s1.memDomain _ _ hb2'
      (encodeInsn_conditionalCompareImmediate false 0 0 resultCarry false false true false
        (by decide))
      (decode_encode_conditionalCompareImmediate false 0 0 resultCarry false false true false
        (by decide) (by decide) hlt2)
      (by rfl)
  have hsafe2 : StepSafe s1.memDomain (t 2) := by
    have hb3' : bytesInMemoryHOL (carryT2 s1 ms sourceRight resultCarry).pc
        (encodeBytes (.addSubCarry false true sourceLeft resultCarry destination))
        (carryT2 s1 ms sourceRight resultCarry).mem s1.memDomain := by
      rw [carryT2_pc, carryT2_mem]
      exact hb3
    exact stepSafe_of_encode (carryT2 s1 ms sourceRight resultCarry) s1.memDomain _ _ hb3'
      (encodeInsn_addSubCarry false true sourceLeft resultCarry destination)
      (decode_encode_addSubCarry false true sourceLeft resultCarry destination hlt3 hlt2 hlt1)
      (by rfl)
  have hsafe3 : StepSafe s1.memDomain (t 3) := by
    have hb4' : bytesInMemoryHOL
        (carryT3 s1 ms sourceRight resultCarry sourceLeft destination).pc
        (encodeBytes (.moveWide .z 0 0 sourceRight))
        (carryT3 s1 ms sourceRight resultCarry sourceLeft destination).mem s1.memDomain := by
      rw [carryT3_pc, carryT3_mem]
      exact hb4
    exact stepSafe_of_encode
      (carryT3 s1 ms sourceRight resultCarry sourceLeft destination) s1.memDomain _ _ hb4'
      (encodeInsn_moveWide .z 0 0 sourceRight)
      (decode_encode_moveWide .z 0 0 sourceRight (by decide) (by decide) hlt4) (by rfl)
  have hsafe4 : StepSafe s1.memDomain (t 4) := by
    have hb5' : bytesInMemoryHOL
        (carryT4 s1 ms sourceRight resultCarry sourceLeft destination).pc
        (encodeBytes (.addSubCarry false false 31 sourceRight sourceRight))
        (carryT4 s1 ms sourceRight resultCarry sourceLeft destination).mem s1.memDomain := by
      rw [carryT4_pc, carryT4_mem]
      exact hb5
    exact stepSafe_of_encode
      (carryT4 s1 ms sourceRight resultCarry sourceLeft destination) s1.memDomain _ _ hb5'
      (encodeInsn_addSubCarry false false 31 sourceRight sourceRight)
      (decode_encode_addSubCarry false false 31 sourceRight sourceRight (by decide) hlt4 hlt4)
      (by rfl)
  have hstate : ∀ k, 1 ≤ k → k ≤ 4 → arm8StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧
      (t k).pc = ms.pc + BitVec.ofNat 64 (k * 4) := by
    intro k h1 h2
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with hk | hk | hk | hk
    · subst hk
      have ht : t 1 = carryT1 s1 ms sourceRight := rfl
      rw [ht]
      refine ⟨?_, ?_, ?_⟩
      · refine arm8StateOk_set _ ?_ ?_
        · rw [carryT1_pc]; exact hal1
        · rw [carryT1_failed]; exact st.msFailed
      · intro x; rw [carryT1_mem]
      · rw [carryT1_pc]
        bv_omega
    · subst hk
      have ht : t 2 = carryT2 s1 ms sourceRight resultCarry := rfl
      rw [ht]
      refine ⟨?_, ?_, ?_⟩
      · refine arm8StateOk_set _ ?_ ?_
        · rw [carryT2_pc]; exact hal2
        · rw [carryT2_failed]; exact st.msFailed
      · intro x; rw [carryT2_mem]
      · rw [carryT2_pc]
        bv_omega
    · subst hk
      have ht : t 3 = carryT3 s1 ms sourceRight resultCarry sourceLeft destination := rfl
      rw [ht]
      refine ⟨?_, ?_, ?_⟩
      · refine arm8StateOk_set _ ?_ ?_
        · rw [carryT3_pc]; exact hal3
        · rw [carryT3_failed]; exact st.msFailed
      · intro x; rw [carryT3_mem]
      · rw [carryT3_pc]
        bv_omega
    · subst hk
      have ht : t 4 = carryT4 s1 ms sourceRight resultCarry sourceLeft destination := rfl
      rw [ht]
      refine ⟨?_, ?_, ?_⟩
      · refine arm8StateOk_set _ ?_ ?_
        · rw [carryT4_pc]; exact hal4
        · rw [carryT4_failed]; exact st.msFailed
      · intro x; rw [carryT4_mem]
      · rw [carryT4_pc]
        bv_omega
  have hsafe : ∀ k, k ≤ 4 → StepSafe s1.memDomain (t k) := by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with hk | hk | hk | hk | hk <;>
      subst hk
    · exact hsafe0
    · exact hsafe1
    · exact hsafe2
    · exact hsafe3
    · exact hsafe4
  have hq : targetStateRel arm8Target s2 (t (4 + 1)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show arm8StateOk (carryT5 s1 ms sourceRight resultCarry sourceLeft destination) = true
      refine arm8StateOk_set _ ?_ ?_
      · rw [carryT5_pc]; exact hal5
      · rw [carryT5_failed]; exact st.msFailed
    · show (carryT5 s1 ms sourceRight resultCarry sourceLeft destination).pc = s2.pc
      rw [carryT5_pc, st.pc, hs2pc]
      bv_omega
    · intro x hx
      show (carryT5 s1 ms sourceRight resultCarry sourceLeft destination).mem x = s2.mem x
      rw [carryT5_mem, hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro j hj
      show arm8Target.getReg (carryT5 s1 ms sourceRight resultCarry sourceLeft destination) j
        = s2.regs j
      have hget : arm8Target.getReg
          (carryT5 s1 ms sourceRight resultCarry sourceLeft destination) j
          = (carryT5 s1 ms sourceRight resultCarry sourceLeft destination).regs j := rfl
      rw [hget, carryT5_regs _ _ _ _ _ _ hne31_4 hne31_1]
      have hs := hs2regs j
      by_cases hjs : j = sourceRight
      · rw [ite_eq_left hjs] at hs ⊢
        rw [hs]
      · rw [ite_eq_right hjs] at hs ⊢
        by_cases hjd : j = destination
        · rw [ite_eq_left hjd] at hs ⊢
          exact hs.symm
        · rw [ite_eq_right hjd] at hs ⊢
          rw [st.reg j hj]
          exact hs.symm
    · intro j hj
      simp only [arm8Target_config, arm8Config] at hj
      omega
  have hstep : ∀ k, k ≤ 4 → arm8Next (t k) = t (k + 1) := by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with hk | hk | hk | hk | hk <;>
      subst hk
    · exact hstep1
    · exact hstep2
    · exact hstep3
    · exact hstep4
    · exact hstep5
  have ht0 : t 0 = ms := rfl
  exact arithRunCase _ s1 s2 ms 4 t ⟨h.1, h.2⟩ ht0 hlen hstep hstate hsafe hs2dom hq

/-! ## The unavailable operations -/

/-- `arm8Config` rejects `longDiv`: the exact side condition requires the
`x86_64` architecture. -/
theorem arm8LongDiv_ok_false (r1 r2 r3 r4 r5 : Nat) :
    asmArithOkExact (.longDiv r1 r2 r3 r4 r5) arm8Config = false := by
  simp only [asmArithOkExact, arm8_isa_x86, Bool.false_and]

/-- `arm8Config` has no floating-point registers, so `fp_ok` is impossible. -/
theorem arm8FpRegOk_false (r : Nat) : asmFpRegOkExact r arm8Config = false := by
  simp only [asmFpRegOkExact, arm8Config]
  exact decide_eq_false (Nat.not_lt_zero r)

/-- `arm8Config` rejects every `fp` operation. -/
theorem arm8FpOk_false (operation : HolFp) : asmFpOkExact operation arm8Config = false := by
  cases operation <;>
    simp only [asmFpOkExact, arm8FpRegOk_false, Bool.and_false]

/-- `longDiv` is unavailable: `arm8Ast` lowers it to `noOp`, and `asm_step`'s
`asm_ok` conjunct is false because `longDiv` requires the `x86_64` architecture.
The case is therefore vacuous. -/
theorem case_longDiv (r1 r2 r3 r4 r5 : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s1 s2 ms := by
  have hok := (arm8Start _ s1 s2 ms h).asmOk
  simp only [asmOkExact, asmInstOkExact] at hok
  rw [arm8LongDiv_ok_false] at hok
  exact Bool.noConfusion hok

/-- Floating point is unavailable: `arm8Ast` lowers `.fp` to `noOp`, and
`asm_step`'s `asm_ok` conjunct is false because `arm8Config.fpRegCount = 0`
makes every `fp_ok` clause false.  The case is therefore vacuous. -/
theorem case_fp (f : HolFp) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.fp f)) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.fp f)) s1 s2 ms := by
  have hok := (arm8Start _ s1 s2 ms h).asmOk
  simp only [asmOkExact, asmInstOkExact] at hok
  rw [arm8FpOk_false f] at hok
  exact Bool.noConfusion hok

end Flapjack.Compiler.Encoders.Arm8
