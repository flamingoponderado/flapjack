module

public import Flapjack.Compiler.Encoders.X64.Machine.ShiftCase

@[expose] public section

/-!
# The `longMul` case of `encoder_correct x64Target`

`arith (longMul r1 r2 r3 r4)` lowers to `mul r4`; `asm_ok` forces
`r1 = 2` (rdx, high half), `r2 = 0` (rax, low half) and `r3 = 0`, so the
instruction's implicit `rdx:rax` product is exactly the source semantics'
two-register result.  The 128-bit product's low half is `setWidth 64` and its
high half is `(p >>> 64).setWidth 64`, which `mul_low`/`mul_high` identify with
`ofNat 64 (x * y)` and `ofNat 64 (x * y / 2^64)`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- The product of two 64-bit words fits in 128 bits. -/
theorem mul_lt_pow128 (x y : BitVec 64) : x.toNat * y.toNat < 2 ^ 128 := by
  calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' x.isLt y.isLt
    _ = 2 ^ 128 := by norm_num

/-- The low 64 bits of the unsigned 128-bit product. -/
theorem mul_low (a b : BitVec 64) :
    (a.setWidth 128 * b.setWidth 128).setWidth 64 =
      BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  have ha : a.toNat < 2 ^ 128 := by have := a.isLt; omega
  have hb : b.toNat < 2 ^ 128 := by have := b.isLt; omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 128)]

/-- The high 64 bits of the unsigned 128-bit product. -/
theorem mul_high (a b : BitVec 64) :
    (let p : BitVec 128 := a.setWidth 128 * b.setWidth 128
     (p >>> 64).setWidth 64) = BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  rw [show ((a.setWidth 128 * b.setWidth 128) >>> 64).setWidth 64 =
      (a.setWidth 128 * b.setWidth 128).extractLsb' 64 64 from rfl]
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  have ha : a.toNat < 2 ^ 128 := by have := a.isLt; omega
  have hb : b.toNat < 2 ^ 128 := by have := b.isLt; omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (mul_lt_pow128 a b)]

/-- `asm_ok` of a `longMul` splits into its register checks and the fixed
`rdx`/`rax`/source registers. -/
theorem longMul_ok (r1 r2 r3 r4 : Nat)
    (h : asmOkExact (.inst (.arith (.longMul r1 r2 r3 r4))) x64Config = true) :
    asmRegOkExact r1 x64Config = true ∧ asmRegOkExact r2 x64Config = true ∧
      asmRegOkExact r3 x64Config = true ∧ asmRegOkExact r4 x64Config = true ∧
      r1 = 2 ∧ r2 = 0 ∧ r3 = 0 := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true] at h
  simp at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩

/-- The `longMul` encoding is the single `mul`. -/
theorem x64Enc_longMul (r1 r2 r3 r4 : Nat)
    (h : asmOkExact (.inst (.arith (.longMul r1 r2 r3 r4))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.longMul r1 r2 r3 r4))) =
      encodeInsn (.mul .z64 r4) := by
  obtain ⟨-, -, -, hr4ok, -, -, -⟩ := longMul_ok r1 r2 r3 r4 h
  have hr4 : r4 < 16 := jumpReg_reg_lt r4 hr4ok
  have hsrc : totalNum2Zreg r4 = r4 := totalNum2Zreg_eq r4 hr4
  have hflat : (x64Ast (.inst (.arith (.longMul r1 r2 r3 r4)))).flatMap encodeInsn =
      encodeInsn (.mul .z64 r4) := by
    simp only [x64Ast, x64Inst, hsrc]
    simp
  have hne : encodeInsn (.mul .z64 r4) ≠ [] := by
    interval_cases r4 <;> simp [encodeInsn, eGenRmReg, eModRM]
  exact x64Enc_of_flatMap _ _ hflat hne

/-- The closed model executes `mul`. -/
theorem execInsn_mul (src : Nat) (len : Nat) (s : X64State) :
    execInsn (.mul .z64 src) len s =
      (let p : BitVec 128 := (readReg s 0).setWidth 128 * (readReg s src).setWidth 128
       let hi : BitVec 64 := (p >>> 64).setWidth 64
       let s' := writeReg (writeReg s 0 (p.setWidth 64)) 2 hi
       { s' with flags := { s.flags with cf := hi ≠ 0, of := hi ≠ 0 } }) := by
  simp only [execInsn]

/-- One `x64Next` step over `mul` writes the product's halves to `rax`/`rdx`. -/
theorem x64Next_mul (ms : X64State) (d : BitVec 64 → Prop) (src : Nat) (hs : src < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.mul .z64 src)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms =
      (let p : BitVec 128 := (readReg ms 0).setWidth 128 * (readReg ms src).setWidth 128
       let hi : BitVec 64 := (p >>> 64).setWidth 64
       { (writeReg (writeReg ms 0 (p.setWidth 64)) 2 hi) with
         flags := { ms.flags with cf := hi ≠ 0, of := hi ≠ 0 },
         pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.mul .z64 src)).length }) := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.mul .z64 src, (encodeInsn (.mul .z64 src)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_mul_z64 src hs) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn]

/-- The `longMul` constructor of `encoder_correct x64Target`: one `x64Next`
step writes the product's low half to `rax` and its high half to `rdx`. -/
theorem case_longMul (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.longMul r1 r2 r3 r4))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.longMul r1 r2 r3 r4))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.longMul r1 r2 r3 r4))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨-, -, -, hr4ok, hr1, hr2, hr3⟩ := longMul_ok r1 r2 r3 r4 hok
  have hr4 : r4 < 16 := jumpReg_reg_lt r4 hr4ok
  have hreg4 := regOk_of_asmRegOk r4 hr4ok
  have hreg0 : 0 < x64Target.config.regCount ∧
      x64Target.config.avoidRegs.contains 0 = false := by decide
  have hreg2 : 2 < x64Target.config.regCount ∧
      x64Target.config.avoidRegs.contains 2 = false := by decide
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (encodeInsn (.mul .z64 r4)).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [x64Enc_longMul r1 r2 r3 r4 hok]
  have hs2regs : ∀ x, s2.regs x =
      if x = 0 then BitVec.ofNat 64 ((s1.regs 0).toNat * (s1.regs r4).toNat)
      else if x = 2 then BitVec.ofNat 64 ((s1.regs 0).toNat * (s1.regs r4).toNat / 2 ^ 64)
      else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg, AsmSem.readReg, hr1, hr2, hr3]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.mul .z64 r4)) ms.mem s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_longMul r1 r2 r3 r4 hok] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode
      (.inst (.arith (.longMul r1 r2 r3 r4)))).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.mul .z64 r4, (encodeInsn (.mul .z64 r4)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm
      (decode_mul_z64 r4 hr4) (by omega)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.mul .z64 r4, _, hdec, ?_, ?_⟩
    · intro j hj; exact hdomN j hj
    · intro a ha; simp [x64Touched] at ha
  have hread0 : readReg ms 0 = s1.regs 0 := st.reg 0 hreg0
  have hread4 : readReg ms r4 = s1.regs r4 := st.reg r4 hreg4
  have hlow : ((readReg ms 0).setWidth 128 * (readReg ms r4).setWidth 128).setWidth 64 =
      BitVec.ofNat 64 ((s1.regs 0).toNat * (s1.regs r4).toNat) := by
    rw [hread0, hread4]
    exact mul_low (s1.regs 0) (s1.regs r4)
  have hhigh : (let p : BitVec 128 := (readReg ms 0).setWidth 128 * (readReg ms r4).setWidth 128
      (p >>> 64).setWidth 64) =
      BitVec.ofNat 64 ((s1.regs 0).toNat * (s1.regs r4).toNat / 2 ^ 64) := by
    dsimp only
    rw [hread0, hread4]
    exact mul_high (s1.regs 0) (s1.regs r4)
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [x64Next_mul ms s1.memDomain r4 hr4 hbm st.failed]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 (encodeInsn (.mul .z64 r4)).length = s2.pc
      rw [st.pc, hs2pc]
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro x hx
      show readReg (writeReg (writeReg ms 0
          (((readReg ms 0).setWidth 128 * (readReg ms r4).setWidth 128).setWidth 64)) 2
          (let p : BitVec 128 := (readReg ms 0).setWidth 128 * (readReg ms r4).setWidth 128
           (p >>> 64).setWidth 64)) x = s2.regs x
      have hmod : x % 16 = x := Nat.mod_eq_of_lt hx.1
      rw [hlow, hhigh]
      simp only [readReg, writeReg, num2Zreg, hmod, Nat.reduceMod]
      rw [hs2regs x]
      by_cases hx0 : x = 0
      · subst hx0
        simp
      · by_cases hx2 : x = 2
        · subst hx2
          simp [hx0]
        · simp only [hx0, hx2, if_false]
          simpa [readReg, num2Zreg, hmod] using st.reg x hx
    · intro x hx
      show readXmm ms x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x hx
  exact encoderCaseStep _ s1 s2 ms 0 hdom hcode
    (by
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      simpa using hstepSafe)
    (by intro k hk1 hk2; omega) hq

end Flapjack.Compiler.Encoders.X64

