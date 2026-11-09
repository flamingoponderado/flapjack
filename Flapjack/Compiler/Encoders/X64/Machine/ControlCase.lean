module

public import Flapjack.Compiler.Encoders.X64.Machine.SkipCase
public import Flapjack.Compiler.Encoders.X64.Machine.TargetProof
public import Flapjack.Compiler.Encoders.X64.Machine.MemDecodeProof

@[expose] public section

/-!
# The `jump` case of `encoder_correct x64Target`

`jump target` lowers to the single instruction `.jcc .zAlways (target - 5)`,
which encodes to a five-byte near jump (`0xE9` and a four-byte immediate) once
`asm_ok`'s jump-offset window accepts the target (`EncodingProof.lean`).  The
closed model's `jcc` adds its own length plus the immediate to `PC`, so one
step lands at `pc + target`, matching
`asmUpd (.jump target) _ s = updPc (s.pc + target) s`.

This file proves the `jump` constructor of `encoderCorrect x64Target`; the
remaining constructors are not yet proved.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- The `jump` encoding is the five-byte near jump under `asm_ok`. -/
theorem x64Enc_jump (target : BitVec 64)
    (h : asmJumpOffsetOkExact x64Config target = true) :
    x64Target.config.encode (.jump target) = encodeInsn (.jcc .zAlways (target - 5)) := by
  show x64Enc (.jump target) = encodeInsn (.jcc .zAlways (target - 5))
  unfold x64Enc x64Ast
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  split
  · rename_i hnil
    have hl5 := x64Enc_jump_length target (by simpa [asmOkExact] using h)
    simp only [x64Enc, x64Ast, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl5
    rw [hnil] at hl5
    simp at hl5
  · rfl

/-- The `jump` encoding is five bytes long. -/
theorem x64Enc_jump_target_length (target : BitVec 64)
    (h : asmJumpOffsetOkExact x64Config target = true) :
    (x64Target.config.encode (.jump target)).length = 5 := by
  have := x64Enc_jump_length target (by simpa [asmOkExact] using h)
  simpa [x64Config_encode] using this

/-- One `x64Next` step from a state whose bytes are the jump encoding lands at
`pc + target`. -/
theorem x64Next_jump (ms : X64State) (d : BitVec 64 → Prop) (target : BitVec 64)
    (hok : asmJumpOffsetOkExact x64Config target = true)
    (hbm : bytesInMemoryHOL ms.pc (x64Target.config.encode (.jump target)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with pc := ms.pc + BitVec.ofNat 64 5 + (target - 5) } := by
  obtain ⟨hlo, hhi⟩ := jump_offset_range target hok
  have hr := jump_offset_sub_five target hlo hhi
  have hlen5 : (x64Target.config.encode (.jump target)).length = 5 :=
    x64Enc_jump_target_length target hok
  rw [x64Enc_jump target hok] at hbm
  rw [x64Enc_jump target hok] at hlen5
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.jcc .zAlways (target - 5), 5) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ 5 hbm
      (decode_jcc_always (target - 5) hr.1 hr.2) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, evalCond, reduceIte]

/-! ## The `jump` case -/

/-- The `jump` constructor of `encoder_correct x64Target`: one `x64Next` step
from a state holding the five jump bytes lands at `pc + target`. -/
theorem case_jump (target : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.jump target) s2 ∧ targetStateRel x64Target s1 ms) :
    CaseGoal (.jump target) s1 s2 ms := by
  have st := x64Start (.jump target) s1 s2 ms h
  have hok : asmJumpOffsetOkExact x64Config target = true := by
    simpa [asmOkExact] using st.asmOk
  have hlen : (x64Target.config.encode (.jump target)).length = 5 :=
    x64Enc_jump_target_length target hok
  have hupd : asmUpd (.jump target) (s1.pc + BitVec.ofNat 64 5) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + target := by
    rw [← hupd]; rfl
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← hupd]; intro a; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ r, s2.regs r = s1.regs r := by
    rw [← hupd]; intro r; rfl
  have hs2fp : ∀ r, s2.fpRegs r = s1.fpRegs r := by
    rw [← hupd]; intro r; rfl
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (x64Target.config.encode (.jump target)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    exact st.bytesTarget
  have hdom5 := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hbm' : bytesInMemoryHOL ms.pc (encodeInsn (.jcc .zAlways (target - 5))) ms.mem
      s1.memDomain := by
    rw [x64Enc_jump target hok] at hbm
    exact hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.jcc .zAlways (target - 5), 5) := by
    have hlen' : (encodeInsn (.jcc .zAlways (target - 5))).length = 5 := by
      have h5 := hlen
      rwa [x64Enc_jump target hok] at h5
    obtain ⟨hlo, hhi⟩ := jump_offset_range target hok
    have hr := jump_offset_sub_five target hlo hhi
    exact decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ 5 hbm'
      (decode_jcc_always _ hr.1 hr.2) (by omega)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.jcc .zAlways (target - 5), 5, hdec, ?_, ?_⟩
    · intro j hj
      exact hdom5 j (by omega)
    · intro a ha
      simp [x64Touched] at ha
  have hnext : x64Next ms = { ms with pc := ms.pc + BitVec.ofNat 64 5 + (target - 5) } :=
    x64Next_jump ms s1.memDomain target hok hbm st.failed
  have hcode : allPcs (x64Target.config.encode (.jump target)).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 5 + (target - 5) = s2.pc
      rw [st.pc, hs2pc]
      bv_omega
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro r hr
      show readReg ms r = s2.regs r
      rw [hs2regs r]
      exact st.reg r hr
    · intro r hr
      show readXmm ms r = s2.fpRegs r
      rw [hs2fp r]
      exact st.fp r hr
  have hsafe : ∀ k ≤ 0, StepSafe s1.memDomain (x64Next^[k] ms) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hstepSafe
  exact encoderCaseStep (.jump target) s1 s2 ms 0 hdom hcode hsafe
    (by intro k hk1 hk2; omega) hq

end Flapjack.Compiler.Encoders.X64
