module

public import Flapjack.Compiler.Encoders.X64.Machine.VacuousCase
public import Flapjack.Compiler.Encoders.X64.Machine.MemDecodeProof

@[expose] public section

/-!
# The `loc` case of `encoder_correct x64Target`

`loc r offset` lowers to the single instruction `.lea .z64 r (offset - 7)`,
which encodes to the seven-byte RIP-relative `lea` once `asm_ok`'s register and
`Loc`-offset checks hold.  The closed model's `lea` adds its own length and the
displacement to `PC`, so it writes `pc + offset` and advances `PC` by seven,
matching `asmUpd (.loc r offset) pc s = updPc pc (updReg r (s.pc + offset) s)`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `asm_ok`'s register check bounds the `Loc` register. -/
theorem loc_reg_lt (r : Nat) (h : asmRegOkExact r x64Config = true) : r < 16 := by
  simp only [asmRegOkExact, x64Config, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- `asm_ok` of a `Loc` splits into its register and offset checks. -/
theorem loc_ok (r : Nat) (off : BitVec 64)
    (h : asmOkExact (.loc r off) x64Config = true) :
    asmRegOkExact r x64Config = true ∧ asmLocOffsetOkExact x64Config off = true := by
  simpa [asmOkExact, x64Config] using h

/-- The `loc` encoding is the seven-byte `lea` under `asm_ok`. -/
theorem x64Enc_loc (r : Nat) (off : BitVec 64)
    (h : asmOkExact (.loc r off) x64Config = true) :
    x64Target.config.encode (.loc r off) = encodeInsn (.lea .z64 r (off - 7)) := by
  obtain ⟨hr, hoff⟩ := loc_ok r off h
  have hd := loc_reg_lt r hr
  have hdst := totalNum2Zreg_eq r hd
  obtain ⟨hlo, hhi⟩ := loc_offset_range off hoff
  have hsub := loc_offset_sub_seven off hlo hhi
  have henc : encodeInsn (.lea .z64 r (off - 7)) = leaBytes r (off - 7) :=
    encodeInsn_lea r hd (off - 7) hsub.1 hsub.2
  have hne : encodeInsn (.lea .z64 r (off - 7)) ≠ [] := by
    rw [henc]; simp [leaBytes]
  have hflat : (x64Ast (.loc r off)).flatMap encodeInsn =
      encodeInsn (.lea .z64 r (off - 7)) := by
    simp only [x64Ast]
    rw [hdst]
    simp
  exact x64Enc_of_flatMap (.loc r off) _ hflat hne

/-- One `x64Next` step from a state whose bytes are the `loc` encoding writes
`pc + offset` to the register and advances `PC` by seven. -/
theorem x64Next_loc (ms : X64State) (d : BitVec 64 → Prop) (r : Nat) (off : BitVec 64)
    (hok : asmOkExact (.loc r off) x64Config = true)
    (hbm : bytesInMemoryHOL ms.pc (x64Target.config.encode (.loc r off)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r (ms.pc + BitVec.ofNat 64 7 + (off - 7))) with
        pc := ms.pc + BitVec.ofNat 64 7 } := by
  obtain ⟨hr, hoff⟩ := loc_ok r off hok
  have hd := loc_reg_lt r hr
  have hdst := totalNum2Zreg_eq r hd
  obtain ⟨hlo, hhi⟩ := loc_offset_range off hoff
  have hsub := loc_offset_sub_seven off hlo hhi
  have hlen : (x64Target.config.encode (.loc r off)).length = 7 := x64Enc_loc_length r off hok
  rw [x64Enc_loc r off hok] at hbm
  rw [x64Enc_loc r off hok] at hlen
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.lea .z64 r (off - 7), 7) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ 7 hbm
      (decode_lea r hd (off - 7) hsub.1 hsub.2) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn,
    writeRegSized, writeReg]

/-! ## The `loc` case -/

/-- The `loc` constructor of `encoder_correct x64Target`. -/
theorem case_loc (r : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.loc r off) s2 ∧ targetStateRel x64Target s1 ms) :
    CaseGoal (.loc r off) s1 s2 ms := by
  have st := x64Start (.loc r off) s1 s2 ms h
  have hok : asmOkExact (.loc r off) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hr, hoff⟩ := loc_ok r off hok
  have hd := loc_reg_lt r hr
  have hlen : (x64Target.config.encode (.loc r off)).length = 7 := x64Enc_loc_length r off hok
  have hupd : asmUpd (.loc r off) (s1.pc + BitVec.ofNat 64 7) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 7 := by
    rw [← hupd]; rfl
  have hs2regs : ∀ x, s2.regs x = if x = r then s1.pc + off else s1.regs x := by
    rw [← hupd]; intro x; rfl
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← hupd]; intro a; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← hupd]; intro x; rfl
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (x64Target.config.encode (.loc r off)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    exact st.bytesTarget
  have hdom7 := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hbm' : bytesInMemoryHOL ms.pc (encodeInsn (.lea .z64 r (off - 7))) ms.mem
      s1.memDomain := by
    rw [x64Enc_loc r off hok] at hbm
    exact hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.lea .z64 r (off - 7), 7) := by
    have hlen' : (encodeInsn (.lea .z64 r (off - 7))).length = 7 := by
      have h7 := hlen
      rwa [x64Enc_loc r off hok] at h7
    exact decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ 7 hbm'
      (decode_lea r hd (off - 7) (loc_offset_sub_seven off
        (loc_offset_range off hoff).1 (loc_offset_range off hoff).2).1
        (loc_offset_sub_seven off
        (loc_offset_range off hoff).1 (loc_offset_range off hoff).2).2) (by omega)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.lea .z64 r (off - 7), 7, hdec, ?_, ?_⟩
    · intro j hj
      exact hdom7 j (by omega)
    · intro a ha
      simp [x64Touched] at ha
  have hnext : x64Next ms =
      { (writeReg ms r (ms.pc + BitVec.ofNat 64 7 + (off - 7))) with
        pc := ms.pc + BitVec.ofNat 64 7 } :=
    x64Next_loc ms s1.memDomain r off hok hbm st.failed
  have hcode : allPcs (x64Target.config.encode (.loc r off)).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [x64Target_stateOk, x64StateOk, writeReg, st.failed]
    · show ms.pc + BitVec.ofNat 64 7 = s2.pc
      rw [st.pc, hs2pc]
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro i hi
      have hi16 : i < 16 := hi.1
      show readReg { (writeReg ms r (ms.pc + BitVec.ofNat 64 7 + (off - 7))) with
          pc := ms.pc + BitVec.ofNat 64 7 } i = s2.regs i
      rw [hs2regs i]
      by_cases hir : i = r
      · subst hir
        simp only [readReg, writeReg, reduceIte]
        rw [st.pc]
        bv_omega
      · have hne : num2Zreg i ≠ num2Zreg r := by
          simp only [num2Zreg]
          rw [Nat.mod_eq_of_lt hi16, Nat.mod_eq_of_lt hd]
          exact hir
        simp only [readReg, writeReg, if_neg hne, if_neg hir]
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
  exact encoderCaseStep (.loc r off) s1 s2 ms 0 hdom hcode hsafe
    (by intro k hk1 hk2; omega) hq

end Flapjack.Compiler.Encoders.X64
