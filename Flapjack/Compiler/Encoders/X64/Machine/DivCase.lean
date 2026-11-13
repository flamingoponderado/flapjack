module

public import Flapjack.Compiler.Encoders.X64.Machine.MulCase

@[expose] public section

/-!
# The `longDiv` case of `encoder_correct x64Target`

`arith (longDiv r1 r2 r3 r4 r5)` lowers to `div r5`.  `asm_ok` forces
`r1 = 0` (rax, quotient), `r2 = 2` (rdx, remainder), `r3 = 2` (rdx, high
dividend word) and `r4 = 0` (rax, low dividend word), so the instruction's
implicit `rdx:rax` dividend and its `rax`/`rdx` results are exactly the source
semantics' quotient and remainder.  `asm_step` also carries `¬ s2.failed`, which
is exactly the source's `assert` succeeding, so the model's two `div` failure
checks agree with the source assertion.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `asm_ok` of a `longDiv` fixes the `rdx`/`rax` operand registers and checks
the divisor. -/
theorem longDiv_ok (r1 r2 r3 r4 r5 : Nat)
    (h : asmOkExact (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) x64Config = true) :
    r1 = 0 ∧ r2 = 2 ∧ r3 = 2 ∧ r4 = 0 ∧ asmRegOkExact r5 x64Config = true := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config,
    Bool.and_eq_true] at h
  simp at h
  obtain ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩ := h
  exact ⟨hr1, hr2, hr3, hr4, hr5⟩

/-- The `longDiv` encoding is the single `div`. -/
theorem x64Enc_longDiv (r1 r2 r3 r4 r5 : Nat)
    (h : asmOkExact (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) =
      encodeInsn (.div .z64 r5) := by
  obtain ⟨-, -, -, -, hr5ok⟩ := longDiv_ok r1 r2 r3 r4 r5 h
  have hr5 : r5 < 16 := jumpReg_reg_lt r5 hr5ok
  have hsrc : totalNum2Zreg r5 = r5 := totalNum2Zreg_eq r5 hr5
  have hflat : (x64Ast (.inst (.arith (.longDiv r1 r2 r3 r4 r5)))).flatMap encodeInsn =
      encodeInsn (.div .z64 r5) := by
    simp only [x64Ast, x64Inst, hsrc]
    simp
  have hne : encodeInsn (.div .z64 r5) ≠ [] := by
    interval_cases r5 <;> simp [encodeInsn, eGenRmReg, eModRM]
  exact x64Enc_of_flatMap _ _ hflat hne

/-- The closed model executes `div`. -/
theorem execInsn_div (src len : Nat) (s : X64State) :
    execInsn (.div .z64 src) len s =
      (let hi : BitVec 64 := readReg s 2
       let lo : BitVec 64 := readReg s 0
       let d : BitVec 64 := readReg s src
       if d = 0 then { s with failed := true }
       else
         let n := hi.toNat * 2 ^ 64 + lo.toNat
         let q := n / d.toNat
         if q ≥ 2 ^ 64 then { s with failed := true }
         else writeReg (writeReg s 0 (BitVec.ofNat 64 q)) 2 (BitVec.ofNat 64 (n % d.toNat))) := by
  simp only [execInsn]

/-- One `x64Next` step over `div` executes it and advances `PC`. -/
theorem x64Next_div (ms : X64State) (d : BitVec 64 → Prop) (src : Nat) (hs : src < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.div .z64 src)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms =
      { execInsn (.div .z64 src) (encodeInsn (.div .z64 src)).length ms with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.div .z64 src)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.div .z64 src, (encodeInsn (.div .z64 src)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_div_z64 src hs) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec]

/-- The `longDiv` constructor of `encoder_correct x64Target`: one `x64Next`
step divides `rdx:rax` by the divisor and writes the quotient to `rax` and the
remainder to `rdx`, matching the source's `longDiv`. -/
theorem case_longDiv (r1 r2 r3 r4 r5 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hr1, hr2, hr3, hr4, hr5ok⟩ := longDiv_ok r1 r2 r3 r4 r5 hok
  have hr5 : r5 < 16 := jumpReg_reg_lt r5 hr5ok
  have hreg5 := regOk_of_asmRegOk r5 hr5ok
  have hreg0 : 0 < x64Target.config.regCount ∧
      x64Target.config.avoidRegs.contains 0 = false := by decide
  have hreg2 : 2 < x64Target.config.regCount ∧
      x64Target.config.avoidRegs.contains 2 = false := by decide
  set n : Nat := (AsmSem.readReg 2 s1).toNat * 2 ^ 64 + (AsmSem.readReg 0 s1).toNat with hn
  set d : Nat := (AsmSem.readReg r5 s1).toNat with hd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (encodeInsn (.div .z64 r5)).length := by
    rw [← st.upd, x64Enc_longDiv r1 r2 r3 r4 r5 hok]
    rfl
  have hs2regs : ∀ x, s2.regs x =
      if x = 0 then BitVec.ofNat 64 (n / d)
      else if x = 2 then BitVec.ofNat 64 (n % d)
      else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, assertState, updReg, hr1, hr2, hr3, hr4,
      ← hn, ← hd]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]; rfl
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x; rfl
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.div .z64 r5)) ms.mem s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_longDiv r1 r2 r3 r4 r5 hok] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode
      (.inst (.arith (.longDiv r1 r2 r3 r4 r5)))).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.div .z64 r5, (encodeInsn (.div .z64 r5)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm
      (decode_div_z64 r5 hr5) (by omega)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.div .z64 r5, _, hdec, ?_, ?_⟩
    · intro j hj; exact hdomN j hj
    · intro a ha; simp [x64Touched] at ha
  -- the source's `assert` succeeded, so its divisor is nonzero and its quotient
  -- fits in one word
  have hcond : decide (d ≠ 0 ∧ n / d < 2 ^ 64) = true := by
    have hf : s2.failed = false := by simpa using st.ok
    rw [← st.upd] at hf
    simp only [asmUpd, instUpd, updPc, arithUpd, assertState, updReg, hr1, hr2, hr3, hr4,
      ← hn, ← hd] at hf
    cases hcd : decide (d ≠ 0 ∧ n / d < 2 ^ 64)
    · simp only [hcd, Bool.not_false, Bool.true_or] at hf
      exact absurd hf (by simp)
    · rfl
  have hd0 : d ≠ 0 := (of_decide_eq_true hcond).1
  have hqbound : n / d < 2 ^ 64 := (of_decide_eq_true hcond).2
  have hread0 : readReg ms 0 = AsmSem.readReg 0 s1 := st.reg 0 hreg0
  have hread2 : readReg ms 2 = AsmSem.readReg 2 s1 := st.reg 2 hreg2
  have hread5 : readReg ms r5 = AsmSem.readReg r5 s1 := st.reg r5 hreg5
  have hdms : readReg ms r5 ≠ 0 := by
    rw [hread5]
    intro hz
    exact hd0 (by rw [hd, hz]; rfl)
  have hqms : ¬ ((readReg ms 2).toNat * 2 ^ 64 + (readReg ms 0).toNat) /
      (readReg ms r5).toNat ≥ 2 ^ 64 := by
    rw [hread2, hread0, hread5, ← hn, ← hd]
    omega
  have hexec : execInsn (.div .z64 r5) (encodeInsn (.div .z64 r5)).length ms =
      writeReg (writeReg ms 0 (BitVec.ofNat 64 (n / d))) 2 (BitVec.ofNat 64 (n % d)) := by
    rw [execInsn_div]
    dsimp only
    rw [ite_eq_right hdms]
    rw [ite_eq_right hqms]
    rw [hread2, hread0, hread5, ← hn, ← hd]
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [x64Next_div ms s1.memDomain r5 hr5 hbm st.failed, hexec]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 (encodeInsn (.div .z64 r5)).length = s2.pc
      rw [st.pc, hs2pc]
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro x hx
      show readReg (writeReg (writeReg ms 0 (BitVec.ofNat 64 (n / d))) 2
          (BitVec.ofNat 64 (n % d))) x = s2.regs x
      rw [readReg_writeReg _ 2 _ x (by omega) hx.1]
      rw [readReg_writeReg _ 0 _ x (by omega) hx.1]
      rw [hs2regs x]
      by_cases hx0 : x = 0
      · subst hx0
        simp
      · by_cases hx2 : x = 2
        · subst hx2
          simp [hx0]
        · simp only [hx0, hx2, ite_false]
          exact st.reg x hx
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
