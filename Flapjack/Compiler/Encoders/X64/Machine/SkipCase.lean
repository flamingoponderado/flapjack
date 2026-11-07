import Flapjack.Compiler.Encoders.X64.Machine.CaseBase
import Flapjack.Compiler.Encoders.X64.Machine.Simulate
import Flapjack.Compiler.Encoders.X64.Machine.DecodeProof

/-!
# The `skip` case of `encoder_correct x64Target`

`skip` lowers to the single instruction `.nop 1`, which encodes to the one byte
`0x90`.  One `x64Next` step from a state holding those bytes decodes the `nop`,
leaves the state unchanged, and advances `PC` by one — matching
`asmUpd (.inst .skip) (pc + 1)`.

`X64Start` collects the facts every x64 case reads off `asm_step` and the
initial `targetStateRel`; `x64Start` extracts them.  Unlike the ARM8 `Start`,
the encoded-byte fact is stated over the target memory `ms.mem` as well,
obtained from the source bytes with `bytesInMemory_changeMem`.

This file proves one constructor of `encoderCorrect x64Target`; the remaining
constructors are not yet proved.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- The facts every x64 case reads off `asm_step` and the initial target
relation.  The encoded bytes are stated over both the source memory and the
target memory; `asm_step` supplies the former and `targetStateRel`'s memory
agreement moves them across with `bytesInMemory_changeMem`. -/
structure X64Start (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : X64State) : Prop where
  bytes : bytesInMemoryHOL s1.pc (x64Target.config.encode i) s1.mem s1.memDomain
  bytesTarget : bytesInMemoryHOL s1.pc (x64Target.config.encode i) ms.mem s1.memDomain
  pc : ms.pc = s1.pc
  mem : ∀ a, s1.memDomain a → ms.mem a = s1.mem a
  reg : ∀ r, r < x64Target.config.regCount ∧ x64Target.config.avoidRegs.contains r = false →
    readReg ms r = s1.regs r
  fp : ∀ r, r < x64Target.config.fpRegCount → readXmm ms r = s1.fpRegs r
  stateOk : x64StateOk ms = true
  failed : ms.failed = false
  be : s1.be = false
  align : s1.align = 0
  upd : asmUpd i (s1.pc + BitVec.ofNat 64 (x64Target.config.encode i).length) s1 = s2
  ok : ¬ s2.failed
  asmOk : asmOkExact i x64Target.config = true

/-- Extract the start facts from one `asm_step` and the initial target
relation. -/
theorem x64Start (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 i s2 ∧ targetStateRel x64Target s1 ms) :
    X64Start i s1 s2 ms := by
  obtain ⟨⟨hb, -, hbe, hal, hupd, hfail, hok⟩, hst⟩ := h
  obtain ⟨hok', hpc, hmem, hreg, hfp⟩ := hst
  have hfailed : ms.failed = false := by
    simpa [x64StateOk, Bool.not_eq_true'] using hok'
  have hbytesTarget : bytesInMemoryHOL s1.pc (x64Target.config.encode i) ms.mem s1.memDomain :=
    bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (bytesInMemoryHOL_domain _ _ _ _ hb n hn)).symm⟩
  exact {
    bytes := hb
    bytesTarget := hbytesTarget
    pc := hpc
    mem := hmem
    reg := hreg
    fp := hfp
    stateOk := hok'
    failed := hfailed
    be := by simpa [x64Target_config, x64Config] using hbe
    align := by simpa [x64Target_config, x64Config] using hal
    upd := hupd
    ok := hfail
    asmOk := hok
  }

/-- `x64_ast` of `skip` is the single `nop 1`. -/
theorem x64Ast_skip : x64Ast (.inst .skip) = [.nop 1] := rfl

/-- `x64_enc` of `skip` is the one byte `0x90`. -/
theorem x64Enc_skip : x64Target.config.encode (.inst .skip) = encodeInsn (.nop 1) := by
  show x64Enc (.inst .skip) = encodeInsn (.nop 1)
  simp [x64Enc, x64Ast, x64Inst, encodeInsn]

/-- The `skip` encoding is one byte long. -/
theorem x64Enc_skip_length : (x64Target.config.encode (.inst .skip)).length = 1 := by
  rw [x64Enc_skip]
  rfl

/-- One `x64Next` step from a state whose bytes are the `skip` encoding decodes
the `nop`, leaves the state unchanged, and advances `PC` by one. -/
theorem x64Next_skip (ms : X64State) (d : BitVec 64 → Prop)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.nop 1)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with pc := ms.pc + BitVec.ofNat 64 1 } := by
  have hlen : (encodeInsn (.nop 1)).length = 1 := rfl
  have hd : decode (byteListReader (encodeInsn (.nop 1))) = some (.nop 1, 1) :=
    decode_nop_one
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) = some (.nop 1, 1) :=
    decode_bytesInMemory (encodeInsn (.nop 1)) ms.pc ms.mem d (.nop 1) 1 hbm hd (by rw [hlen])
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn]

/-! ## The `skip` case -/

/-- The `skip` constructor of `encoder_correct x64Target`: one `x64Next` step
from a state holding the `nop` byte only advances the PC. -/
theorem case_skip (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst .skip) s2 ∧ targetStateRel x64Target s1 ms) :
    CaseGoal (.inst .skip) s1 s2 ms := by
  have st := x64Start (.inst .skip) s1 s2 ms h
  have hlen : (x64Target.config.encode (.inst .skip)).length = 1 := x64Enc_skip_length
  have hupd : asmUpd (.inst .skip) (s1.pc + BitVec.ofNat 64 1) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 1 := by
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
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.nop 1)) ms.mem s1.memDomain := by
    have h := st.bytesTarget
    rw [x64Enc_skip] at h
    rw [← st.pc] at h
    exact h
  have hdom1 := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) = some (.nop 1, 1) :=
    decode_bytesInMemory (encodeInsn (.nop 1)) ms.pc ms.mem s1.memDomain (.nop 1) 1 hbm
      decode_nop_one (by rfl)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.nop 1, 1, hdec, ?_, ?_⟩
    · intro j hj
      exact hdom1 j hj
    · intro a ha
      simp [x64Touched] at ha
  have hnext : x64Next ms = { ms with pc := ms.pc + BitVec.ofNat 64 1 } :=
    x64Next_skip ms s1.memDomain hbm st.failed
  have hcode : allPcs (x64Target.config.encode (.inst .skip)).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [x64Enc_skip]
    exact bytesInMemory_allPcs (encodeInsn (.nop 1)) s1.pc s1.mem s1.memDomain 0 st.bytes
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 1 = s2.pc
      rw [st.pc, hs2pc]
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
  exact encoderCaseStep (.inst .skip) s1 s2 ms 0 hdom hcode hsafe
    (by intro k hk1 hk2; omega) hq

end Flapjack.Compiler.Encoders.X64
