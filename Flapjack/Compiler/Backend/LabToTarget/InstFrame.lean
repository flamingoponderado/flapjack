import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.LabToTarget.InstUpdates
import Flapjack.Compiler.Encoders.AsmProps.AsmConsts

/-! Flapjack frame infrastructure for the original `Inst_lemma`
(lab_to_targetProofScript.sml:2170-2932). HOL re-establishes each conjunct of
`state_rel_def` after an instruction by simplification; here the conjuncts
that an instruction cannot affect are carried over once, so each instruction
case supplies only its register, FP register, memory and PC facts. None of
these declarations has an independent HOL original. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps Flapjack.Misc

/-- Bytes placed outside the source memory domain survive any target memory
change confined to that domain. -/
theorem bytesInMem_frame {width : Nat} [NeZero width] {Value : Type}
    (a : BitVec width) (xs : List Value) (m m' : BitVec width → Value)
    (dm dm1 : BitVec width → Prop) (hout : ∀ a, ¬ dm1 a → m' a = m a)
    (h : bytesInMemHOL a xs m dm dm1) : bytesInMemHOL a xs m' dm dm1 := by
  induction xs generalizing a with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨hd, hx, hv, ht⟩ := h
    exact ⟨hd, hx, (hout a hx).trans hv, ih (a + 1) ht⟩

/-- The complete relation after an update of only the source registers, FP
registers, memory, PC and clock and of only the target registers, FP
registers, memory and PC. -/
theorem stateRel_frame {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 ms2 : S}
    (h : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (regs : Nat → WordLocW width) (fpRegs : Nat → BitVec 64)
    (memory : BitVec width → WordLocW width) (pc clock : Nat)
    (tregs : Nat → BitVec width) (tfpRegs : Nat → BitVec 64)
    (tmem : BitVec width → BitVec 8) (tpc : BitVec width)
    (htrel : targetStateRel mc.target
      { t1 with regs := tregs, fpRegs := tfpRegs, mem := tmem, pc := tpc } ms2)
    (hregs : ∀ r, wordLocVal p labs (regs r) = some (tregs r))
    (hfp : ∀ r, fpRegs r = tfpRegs r)
    (hmem : ∀ a, s1.memDomain (holByteAlign a) = true →
      wordLocValByte p labs memory a s1.be = some (tmem a))
    (hout : ∀ a, ¬ s1.memDomain a = true → tmem a = t1.mem a)
    (hpc : tpc = p + BitVec.ofNat width (posVal pc 0 code2)) :
    stateRel (mc, code2, labs, p)
      { s1 with regs := regs, fpRegs := fpRegs, memory := memory, pc := pc, clock := clock }
      { t1 with regs := tregs, fpRegs := tfpRegs, mem := tmem, pc := tpc } ms2 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36,
    c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53⟩ := h
  refine ⟨htrel, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, hfp, hregs, ?_, c32,
    bytesInMem_frame _ _ _ _ _ _ hout c33, c34, bytesInMem_frame _ _ _ _ _ _ hout c35, c36,
    c37, c38, c39, c40, hpc, c42, c43, c44, c45, c46, c47, c48, c49,
    shareMemStateRel_of_ffi mc s1 _ t1 ms1 _ ms2 rfl c50, c51, c52, c53⟩
  intro a ha
  obtain ⟨h1, h2, -⟩ := c31 a ha
  exact ⟨h1, h2, hmem a ha⟩

/-- The per-instruction obligations of the original proof, from the
registers, FP registers and memory of the related pre-states: the target
does not fail, its memory changes only inside the source memory domain, and
the post-state registers, FP registers and domain bytes stay related. -/
def InstSim {width : Nat} [NeZero width] {C F : Type} (p : BitVec width)
    (labs : Spt (Spt Nat)) (i : HolInst width) (s1 : LabSem.State width C F)
    (t1 : AsmState width) : Prop :=
  ¬ (AsmSem.instUpd i t1).failed ∧
  (∀ a, ¬ s1.memDomain a = true → (AsmSem.instUpd i t1).mem a = t1.mem a) ∧
  (∀ r, wordLocVal p labs ((asmInst i s1).regs r) = some ((AsmSem.instUpd i t1).regs r)) ∧
  (∀ r, (asmInst i s1).fpRegs r = (AsmSem.instUpd i t1).fpRegs r) ∧
  (∀ a, s1.memDomain (holByteAlign a) = true →
    wordLocValByte p labs (asmInst i s1).memory a s1.be = some ((AsmSem.instUpd i t1).mem a))

/-- The source instruction changes no field outside registers, FP registers,
memory and the failure flag. -/
theorem asmInst_frame {width : Nat} [NeZero width] {C F : Type} (i : HolInst width)
    (s : LabSem.State width C F) :
    (asmInst i s).memDomain = s.memDomain ∧
    (asmInst i s).sharedMemDomain = s.sharedMemDomain ∧
    (asmInst i s).be = s.be ∧
    (asmInst i s).codeBuffer = s.codeBuffer ∧
    (asmInst i s).compile = s.compile ∧
    (asmInst i s).compileOracle = s.compileOracle := by
  cases i with
  | skip => simp [asmInst]
  | const register value => simp [asmInst, LabSem.updReg]
  | arith operation =>
      cases operation <;> simp only [asmInst, LabSem.arithUpd]
      all_goals repeat' first
        | simp_all [LabSem.binopUpd, LabSem.updReg, LabSem.assertState]
        | split
  | mem operator register address =>
      cases operator <;> simp only [asmInst, LabSem.memOp, LabSem.memLoad, LabSem.memStore,
        LabSem.memLoad32, LabSem.memStore32, LabSem.memLoadByte, LabSem.memStoreByte]
      all_goals repeat' first
        | simp_all [LabSem.updReg, LabSem.updMem, LabSem.assertState]
        | split
  | fp operation =>
      cases operation <;> simp only [asmInst, LabSem.fpUpd]
      all_goals repeat' first
        | simp_all [LabSem.updFpReg, LabSem.updReg, LabSem.assertState]
        | split

/-- A successful source instruction followed by the PC and clock steps is a
record update of the original state. -/
theorem incPc_decClock_asmInst_eq {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : LabSem.State width C F) (hs : s.failed = false)
    (hf : ¬ (asmInst i s).failed) :
    incPc (decClock (asmInst i s)) =
      { s with
          regs := (asmInst i s).regs
          fpRegs := (asmInst i s).fpRegs
          memory := (asmInst i s).memory
          pc := s.pc + 1
          clock := s.clock - 1 } := by
  obtain ⟨hpc, hcode, hclock, hffi, hio, hiofp, hcc, hccfp, hptr, hlen, hptr2, hlen2,
    hlink⟩ := asmInstConsts i s
  obtain ⟨hdom, hsdom, hbe, hcb, hcomp, horacle⟩ := asmInst_frame i s
  have hfail : (asmInst i s).failed = false := by simpa using hf
  generalize asmInst i s = s' at *
  cases s; cases s'
  simp_all [incPc, decClock]

/-- A successful target instruction followed by the PC update is a record
update of the original target state. -/
theorem updPc_instUpd_eq {width : Nat} [NeZero width] (i : HolInst width)
    (t : AsmState width) (pc : BitVec width) (ht : t.failed = false)
    (hf : ¬ (AsmSem.instUpd i t).failed) :
    AsmSem.updPc pc (AsmSem.instUpd i t) =
      { t with
          regs := (AsmSem.instUpd i t).regs
          fpRegs := (AsmSem.instUpd i t).fpRegs
          mem := (AsmSem.instUpd i t).mem
          pc := pc } := by
  obtain ⟨hbe, hlr, halign, hdom⟩ := AsmProps.asm_consts (.inst i) pc t
  change (AsmSem.updPc pc (AsmSem.instUpd i t)).be = t.be at hbe
  change (AsmSem.updPc pc (AsmSem.instUpd i t)).lr = t.lr at hlr
  change (AsmSem.updPc pc (AsmSem.instUpd i t)).align = t.align at halign
  change (AsmSem.updPc pc (AsmSem.instUpd i t)).memDomain = t.memDomain at hdom
  simp only [AsmSem.updPc] at hbe hlr halign hdom ⊢
  have hfail : (AsmSem.instUpd i t).failed = false := by simpa using hf
  generalize AsmSem.instUpd i t = t' at *
  cases t; cases t'
  simp_all

end Flapjack.Compiler.Backend.LabToTarget
