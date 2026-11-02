import Flapjack.Compiler.Encoders.X64.Machine.Target
import Flapjack.Misc.SetSep

/-!
# Agreement on the projection of the closed x86-64 machine

Two states agree on a memory domain `d` when they have the same PC, register
file, XMM file, flags, failure flag, and the same bytes on `d`.  This is the
state relation carried by the projection-preserving interference environments
of `encoder_correct`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack

/-- Agreement of two closed x86-64 states on the domain `d`. -/
structure X64Agree (d : BitVec 64 → Prop) (s t : X64State) : Prop where
  pc : s.pc = t.pc
  regs : ∀ r, s.regs r = t.regs r
  xmm : ∀ r, s.xmm r = t.xmm r
  flags : s.flags = t.flags
  failed : s.failed = t.failed
  mem : ∀ a, d a → s.mem a = t.mem a

/-- Agreement is reflexive. -/
theorem X64Agree.refl (d : BitVec 64 → Prop) (s : X64State) : X64Agree d s s :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Agreement is symmetric. -/
theorem X64Agree.symm {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t) :
    X64Agree d t s :=
  ⟨h.pc.symm, fun r => (h.regs r).symm, fun r => (h.xmm r).symm, h.flags.symm, h.failed.symm,
    fun a ha => (h.mem a ha).symm⟩

/-- Agreement is transitive. -/
theorem X64Agree.trans {d : BitVec 64 → Prop} {s t u : X64State}
    (h1 : X64Agree d s t) (h2 : X64Agree d t u) : X64Agree d s u :=
  ⟨h1.pc.trans h2.pc, fun r => (h1.regs r).trans (h2.regs r),
    fun r => (h1.xmm r).trans (h2.xmm r), h1.flags.trans h2.flags, h1.failed.trans h2.failed,
    fun a ha => (h1.mem a ha).trans (h2.mem a ha)⟩

/-- Membership in the projected memory graph. -/
theorem x64Proj_memory (d : BitVec 64 → Prop) (s : X64State)
    (a : BitVec 64) (b : BitVec 8) :
    (x64Proj d s).2.2.2.2.2 (a, b) ↔ s.mem a = b ∧ d a :=
  SetSep.fun2SetThm s.mem d a b

/-- Equal projections are exactly agreeing states. -/
theorem proj_eq_iff (d : BitVec 64 → Prop) (s t : X64State) :
    x64Proj d s = x64Proj d t ↔ X64Agree d s t := by
  constructor
  · intro h
    have hpc : s.pc = t.pc := congrArg Prod.fst h
    have hregs : s.regs = t.regs := congrArg (fun p => p.2.1) h
    have hxmm : s.xmm = t.xmm := congrArg (fun p => p.2.2.1) h
    have hflags : s.flags = t.flags := congrArg (fun p => p.2.2.2.1) h
    have hfailed : s.failed = t.failed := congrArg (fun p => p.2.2.2.2.1) h
    have hmem : (x64Proj d s).2.2.2.2.2 = (x64Proj d t).2.2.2.2.2 :=
      congrArg (fun p => p.2.2.2.2.2) h
    refine ⟨hpc, fun r => congrFun hregs r, fun r => congrFun hxmm r, hflags, hfailed, ?_⟩
    intro a ha
    have hleft : (x64Proj d s).2.2.2.2.2 (a, s.mem a) := by
      rw [x64Proj_memory]; exact ⟨rfl, ha⟩
    rw [hmem] at hleft
    rw [x64Proj_memory] at hleft
    exact hleft.1.symm
  · rintro ⟨hpc, hregs, hxmm, hflags, hfailed, hmem⟩
    have hset : SetSep.fun2Set (s.mem, d) = SetSep.fun2Set (t.mem, d) := by
      funext p
      obtain ⟨a, b⟩ := p
      apply propext
      rw [SetSep.fun2SetThm, SetSep.fun2SetThm]
      exact ⟨fun ⟨hb, ha⟩ => ⟨by rw [← hmem a ha, hb], ha⟩,
        fun ⟨hb, ha⟩ => ⟨by rw [hmem a ha, hb], ha⟩⟩
    simp only [x64Proj, hpc, hflags, hfailed, funext hregs, funext hxmm, hset]

/-- Register reads only depend on the register file. -/
theorem readReg_congr {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t) (r : Nat) :
    readReg s r = readReg t r := by
  simp only [readReg, h.regs]

/-- XMM reads only depend on the XMM file. -/
theorem readXmm_congr {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t) (r : Nat) :
    readXmm s r = readXmm t r := by
  simp only [readXmm, h.xmm]

end Flapjack.Compiler.Encoders.X64
