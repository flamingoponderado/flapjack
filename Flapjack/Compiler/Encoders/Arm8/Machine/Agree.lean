import Flapjack.Compiler.Encoders.Arm8.Machine.Target

/-!
# Agreement on a memory domain for the closed ARMv8 model

`Arm8Agree d s t` says two machine states have the same PC, registers, flags and
failure flag, and the same bytes on `d`. This is exactly what `arm8Proj d`
observes, so it is the state relation an interference environment must preserve.
It is the ARM8 analogue of the MIPS32 `Agree` structure used in that target's
`encoder_correct` proof; the step-preservation lemmas are still to come.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack

/-- Two closed ARMv8 states agree on registers, control state, and the memory
domain `d`. -/
structure Arm8Agree (d : BitVec 64 → Prop) (s t : Arm8State) : Prop where
  pc : s.pc = t.pc
  regs : s.regs = t.regs
  n : s.n = t.n
  z : s.z = t.z
  c : s.c = t.c
  v : s.v = t.v
  failed : s.failed = t.failed
  mem : ∀ a, d a → s.mem a = t.mem a

theorem Arm8Agree.refl (d : BitVec 64 → Prop) (s : Arm8State) : Arm8Agree d s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Arm8Agree.symm {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t) :
    Arm8Agree d t s :=
  ⟨h.pc.symm, h.regs.symm, h.n.symm, h.z.symm, h.c.symm, h.v.symm, h.failed.symm,
    fun a ha => (h.mem a ha).symm⟩

theorem Arm8Agree.trans {d : BitVec 64 → Prop} {s t u : Arm8State}
    (h₁ : Arm8Agree d s t) (h₂ : Arm8Agree d t u) : Arm8Agree d s u :=
  ⟨h₁.pc.trans h₂.pc, h₁.regs.trans h₂.regs, h₁.n.trans h₂.n, h₁.z.trans h₂.z,
    h₁.c.trans h₂.c, h₁.v.trans h₂.v, h₁.failed.trans h₂.failed,
    fun a ha => (h₁.mem a ha).trans (h₂.mem a ha)⟩

theorem fun2Set_eq_iff {f g : BitVec 64 → BitVec 8} {d : BitVec 64 → Prop} :
    SetSep.fun2Set (f, d) = SetSep.fun2Set (g, d) ↔ ∀ a, d a → f a = g a := by
  constructor
  · intro h a ha
    have hm : SetSep.fun2Set (f, d) (a, f a) :=
      (SetSep.fun2SetThm f d a (f a)).2 ⟨rfl, ha⟩
    rw [h] at hm
    exact ((SetSep.fun2SetThm g d a (f a)).1 hm).1.symm
  · intro h
    funext ⟨a, b⟩
    apply propext
    rw [SetSep.fun2SetThm, SetSep.fun2SetThm]
    constructor
    · rintro ⟨rfl, ha⟩; exact ⟨(h a ha).symm, ha⟩
    · rintro ⟨rfl, ha⟩; exact ⟨h a ha, ha⟩

/-- Equal ARM8 projections are exactly `Arm8Agree` states. -/
theorem arm8Proj_eq_iff (d : BitVec 64 → Prop) (s t : Arm8State) :
    arm8Proj d s = arm8Proj d t ↔ Arm8Agree d s t := by
  simp only [arm8Proj, readFlags, Prod.mk.injEq, fun2Set_eq_iff]
  constructor
  · rintro ⟨hpc, ⟨hn, hz, hc, hv⟩, hfailed, hregs, hmem⟩
    exact ⟨hpc, hregs, hn, hz, hc, hv, hfailed, hmem⟩
  · rintro ⟨hpc, hregs, hn, hz, hc, hv, hfailed, hmem⟩
    exact ⟨hpc, ⟨hn, hz, hc, hv⟩, hfailed, hregs, hmem⟩

end Flapjack.Compiler.Encoders.Arm8
