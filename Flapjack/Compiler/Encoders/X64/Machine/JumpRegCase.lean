module

public import Flapjack.Compiler.Encoders.X64.Machine.VacuousCase
public import Flapjack.Compiler.Encoders.X64.Machine.MemDecodeProof
public import Flapjack.Misc.Alignment

@[expose] public section

/-!
# The `jumpReg` case of `encoder_correct x64Target`

`jumpReg r` lowers to the single instruction `.jmp r`, which encodes to the
two- or three-byte indirect near jump `0xFF /4` once `asm_ok`'s register check
holds.  The closed model's `jmp` sets `PC` to the register's value and does not
advance it, matching
`asmUpd (.jumpReg r) _ s = updPc (readReg r s) (assertState (aligned s.align (readReg r s)) s)`:
the source alignment is `0` (`codeAlignment`), so `aligned 0 a` is true and the
assert leaves the state unchanged.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `aligned 0 w` always holds: `2 ^ 0 = 1` divides every `w2n w`. -/
theorem holAligned_zero {width : Nat} [NeZero width] (w : BitVec width) :
    holAligned 0 w = true := by
  rw [holAligned_iff]
  simp [Nat.mod_one]

/-- `asm_ok` of a `jumpReg` is its register check. -/
theorem jumpReg_ok (r : Nat) (h : asmOkExact (.jumpReg r) x64Config = true) :
    asmRegOkExact r x64Config = true := by
  simpa [asmOkExact, x64Config] using h

/-- `asm_ok`'s register check bounds the `jumpReg` register. -/
theorem jumpReg_reg_lt (r : Nat) (h : asmRegOkExact r x64Config = true) : r < 16 := by
  simp only [asmRegOkExact, x64Config, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- `asm_ok`'s register check excludes the reserved registers. -/
theorem jumpReg_reg_avoid (r : Nat) (h : asmRegOkExact r x64Config = true) :
    r ∉ x64Config.avoidRegs := by
  simp only [asmRegOkExact, x64Config, Bool.and_eq_true] at h
  simpa [x64Config] using h.2

/-- The `jumpReg` encoding is nonempty. -/
theorem encodeInsn_jmp_ne_nil (r : Nat) (hr : r < 16) : encodeInsn (.jmp r) ≠ [] := by
  interval_cases r <;> decide

/-- The `jumpReg` encoding is the indirect `jmp` under `asm_ok`. -/
theorem x64Enc_jumpReg (r : Nat) (hr : r < 16) :
    x64Target.config.encode (.jumpReg r) = encodeInsn (.jmp r) := by
  have hdst : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hflat : (x64Ast (.jumpReg r)).flatMap encodeInsn = encodeInsn (.jmp r) := by
    simp only [x64Ast]
    rw [hdst]
    simp
  exact x64Enc_of_flatMap (.jumpReg r) _ hflat (encodeInsn_jmp_ne_nil r hr)

/-- One `x64Next` step from a state whose bytes are the `jumpReg` encoding sets
`PC` to the register's value. -/
theorem x64Next_jumpReg (ms : X64State) (d : BitVec 64 → Prop) (r : Nat) (hr : r < 16)
    (hbm : bytesInMemoryHOL ms.pc (x64Target.config.encode (.jumpReg r)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with pc := readReg ms r } := by
  rw [x64Enc_jumpReg r hr] at hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.jmp r, (encodeInsn (.jmp r)).length) :=
    decode_bytesInMemory (encodeInsn (.jmp r)) ms.pc ms.mem d (.jmp r)
      (encodeInsn (.jmp r)).length hbm (decode_jmp r hr) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn]

/-! ## The `jumpReg` case -/

/-- The `jumpReg` constructor of `encoder_correct x64Target`: one `x64Next` step
from a state holding the indirect jump bytes sets `PC` to the register's value. -/
theorem case_jumpReg (r : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.jumpReg r) s2 ∧ targetStateRel x64Target s1 ms) :
    CaseGoal (.jumpReg r) s1 s2 ms := by
  have st := x64Start (.jumpReg r) s1 s2 ms h
  have hok : asmOkExact (.jumpReg r) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  have hr : r < 16 := jumpReg_reg_lt r (jumpReg_ok r hok)
  have hav : r ∉ x64Config.avoidRegs := jumpReg_reg_avoid r (jumpReg_ok r hok)
  have hreg : r < x64Target.config.regCount ∧ x64Target.config.avoidRegs.contains r = false := by
    refine ⟨?_, ?_⟩
    · simpa [x64Target_config, x64Config] using hr
    · simpa [x64Target_config, x64Config] using hav
  have hs2pc : s2.pc = s1.regs r := by
    rw [← st.upd]
    simp only [asmUpd, AsmSem.readReg, updPc]
  have hs2failed : s2.failed = s1.failed := by
    rw [← st.upd]
    simp only [asmUpd, updPc, assertState, st.align, holAligned_zero, Bool.not_true,
      Bool.false_or]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, updPc, assertState]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, updPc, assertState]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, updPc, assertState]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, updPc, assertState]
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbmConf : bytesInMemoryHOL ms.pc (x64Target.config.encode (.jumpReg r)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    exact st.bytesTarget
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.jmp r)) ms.mem s1.memDomain := by
    have h' := hbmConf
    rw [x64Enc_jumpReg r hr] at h'
    exact h'
  have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.jmp r, (encodeInsn (.jmp r)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm (decode_jmp r hr) (by omega)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.jmp r, (encodeInsn (.jmp r)).length, hdec, ?_, ?_⟩
    · intro j hj
      exact hdomN j hj
    · intro a ha
      simp [x64Touched] at ha
  have hnext : x64Next ms = { ms with pc := readReg ms r } :=
    x64Next_jumpReg ms s1.memDomain r hr hbmConf st.failed
  have hcode : allPcs (x64Target.config.encode (.jumpReg r)).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, st.failed, Bool.not_false]
    · show readReg ms r = s2.pc
      rw [hs2pc]
      exact st.reg r hreg
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro i hi
      show readReg { ms with pc := readReg ms r } i = s2.regs i
      rw [hs2regs i]
      simp only [readReg]
      exact st.reg i hi
    · intro x hx
      show readXmm ms x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x hx
  have hsafe : ∀ k ≤ 0, StepSafe s1.memDomain (x64Next^[k] ms) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hstepSafe
  exact encoderCaseStep (.jumpReg r) s1 s2 ms 0 hdom hcode hsafe
    (by intro k hk1 hk2; omega) hq

end Flapjack.Compiler.Encoders.X64
