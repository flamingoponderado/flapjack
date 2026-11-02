import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Bytes
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

set_option maxHeartbeats 4000000

/-!
# From an interference-free run to `encoder_correct arm8TargetL3`

The L3 analogue of `Flapjack/Compiler/Encoders/Arm8/Machine/Simulate.lean`:
`Arm8L3Agree` records agreement on everything `arm8Proj` observes, and
`arm8Proj_eq_iff` identifies it with equality of the projection.  The
congruence lemmas let a case proof transfer the intermediate assertions and
the post-state relation across an interference environment.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- Agreement of two L3 ARMv8 states on every component `arm8_proj` observes,
plus memory on the source domain. -/
structure Arm8L3Agree (d : BitVec 64 → Prop) (s t : arm8_state) : Prop where
  pc : s.PC = t.PC
  reg : s.REG = t.REG
  pstate : s.PSTATE = t.PSTATE
  sctlr : s.SCTLR_EL1 = t.SCTLR_EL1
  tcr : s.TCR_EL1 = t.TCR_EL1
  exc : s.exception = t.exception
  mem : ∀ a, d a → s.MEM a = t.MEM a

theorem Arm8L3Agree.refl (d : BitVec 64 → Prop) (s : arm8_state) : Arm8L3Agree d s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Arm8L3Agree.symm {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) : Arm8L3Agree d t s :=
  ⟨h.pc.symm, h.reg.symm, h.pstate.symm, h.sctlr.symm, h.tcr.symm, h.exc.symm,
    fun a ha => (h.mem a ha).symm⟩

theorem Arm8L3Agree.trans {d : BitVec 64 → Prop} {s t u : arm8_state}
    (h1 : Arm8L3Agree d s t) (h2 : Arm8L3Agree d t u) : Arm8L3Agree d s u :=
  ⟨h1.pc.trans h2.pc, h1.reg.trans h2.reg, h1.pstate.trans h2.pstate,
    h1.sctlr.trans h2.sctlr, h1.tcr.trans h2.tcr, h1.exc.trans h2.exc,
    fun a ha => (h1.mem a ha).trans (h2.mem a ha)⟩

/-- Equal projections are exactly agreement on the observed components. -/
theorem arm8Proj_eq_iff (d : BitVec 64 → Prop) (s t : arm8_state) :
    arm8Proj d s = arm8Proj d t ↔ Arm8L3Agree d s t := by
  constructor
  · intro h
    have hp : s.PSTATE = t.PSTATE := congrArg (fun p => p.1) h
    have hs : s.SCTLR_EL1 = t.SCTLR_EL1 := congrArg (fun p => p.2.1) h
    have ht : s.TCR_EL1 = t.TCR_EL1 := congrArg (fun p => p.2.2.1) h
    have he : s.exception = t.exception := congrArg (fun p => p.2.2.2.1) h
    have hr : s.REG = t.REG := congrArg (fun p => p.2.2.2.2.1) h
    have hm : (arm8Proj d s).2.2.2.2.2.1 = (arm8Proj d t).2.2.2.2.2.1 :=
      congrArg (fun p => p.2.2.2.2.2.1) h
    have hpc : s.PC = t.PC := congrArg (fun p => p.2.2.2.2.2.2) h
    refine ⟨hpc, hr, hp, hs, ht, he, fun a ha => ?_⟩
    have hleft : (arm8Proj d s).2.2.2.2.2.1 (a, s.MEM a) := by
      rw [arm8Proj_memory]; exact ⟨rfl, ha⟩
    rw [hm, arm8Proj_memory] at hleft
    exact hleft.1.symm
  · intro h
    obtain ⟨hpc, hr, hp, hs, ht, he, hm⟩ := h
    have hmem : SetSep.fun2Set (s.MEM, d) = SetSep.fun2Set (t.MEM, d) := by
      funext p
      obtain ⟨a, b⟩ := p
      apply propext
      rw [SetSep.fun2SetThm, SetSep.fun2SetThm]
      by_cases ha : d a
      · rw [hm a ha]
      · simp [ha]
    simp only [arm8Proj, hp, hs, ht, he, hr, hpc, hmem]

/-- `arm8Ok` only reads the components `Arm8L3Agree` fixes. -/
theorem arm8Ok_congr {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) : arm8Ok s = arm8Ok t := by
  simp only [arm8Ok, h.pstate, h.sctlr, h.tcr, h.exc, h.pc]

/-- `targetStateRel arm8TargetL3` is invariant under agreement on the source
domain. -/
theorem targetStateRel_congr {s2 : AsmState 64} {s t : arm8_state}
    (h : Arm8L3Agree s2.memDomain s t)
    (ht : targetStateRel arm8TargetL3 s2 t) : targetStateRel arm8TargetL3 s2 s := by
  obtain ⟨hok, hp, hmem, hreg, hfp⟩ := ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hok]; exact arm8Ok_congr h
  · rw [← hp]; exact h.pc
  · intro a ha; rw [← hmem a ha]; exact h.mem a ha
  · intro i hi; simpa only [arm8TargetL3_getReg, h.reg] using hreg i hi
  · intro i hi
    simp [arm8ConfigL3] at hi

/-- The conclusion of `encoder_correct` for one source instruction, at
`arm8TargetL3`. -/
def CaseGoal (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : arm8_state) : Prop :=
  ∃ n : Nat, ∀ env : Nat → arm8_state → arm8_state,
    interferenceOk env (arm8Proj s1.memDomain) →
    let pcs := allPcs (arm8ConfigL3.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (arm8Next s)) ms
        (fun ms' => arm8Ok ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → ms'.MEM pc = ms.MEM pc) ∧
          ms'.PC ∈ pcs arm8ConfigL3.codeAlignment)
        (fun ms' => targetStateRel arm8TargetL3 s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) arm8Next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → ms1.MEM x = ms2.MEM x)

/-- One constructor of `encoder_correct arm8TargetL3` from any one-instruction
lowering: the single `arm8Next` step executes `i`, which writes `v` into the
destination register `r` and changes nothing else (Flapjack infrastructure;
the `const` and `arith` one-instruction shapes both use it).  The source-state
update facts are hypotheses because `asmUpd` inspects the instruction. -/
theorem asmCaseOne (inst : HolInst 64) (r : Nat) (v : BitVec 64)
    (t : arm8_state) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst inst) s2 ∧ targetStateRel arm8TargetL3 s1 ms)
    (hnext : arm8Next ms = t)
    (htpc : t.PC = ms.PC + 4)
    (htmem : ∀ x, t.MEM x = ms.MEM x)
    (htreg : ∀ k, k < 32 → k ≠ r → t.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k))
    (htval : t.REG (BitVec.ofNat 5 r) = v)
    (htok : arm8Ok t = true)
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4)
    (hs2mem : ∀ x, s2.mem x = s1.mem x)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ k, s2.regs k = if k = r then v else s1.regs k) :
    CaseGoal (.inst inst) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hq : targetStateRel arm8TargetL3 s2 t := by
    refine ⟨htok, ?_, ?_, ?_, ?_⟩
    · change t.PC = s2.pc
      rw [htpc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → t.MEM a = s2.mem a
      intro a ha
      rw [htmem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        t.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      by_cases hkr : k = r
      · rw [hkr, htval, hs2regs r, if_pos rfl]
      · rw [htreg k hk.1 hkr, hs2regs k, if_neg hkr]
        exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
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

end Flapjack.Compiler.Encoders.Arm8.L3

