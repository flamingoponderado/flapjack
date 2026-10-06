import Flapjack.Mips32.TargetProof.Memory
import Mathlib.Tactic.SplitIfs

/-! # States that agree on a memory domain

`Agree d s t`: the two machine states have the same registers, control state and the same
bytes on the domain `d` — exactly what `mips32Proj d` observes. One `exec` or `mips32Next`
step preserves agreement and leaves the bytes outside `d` alone, provided the step only
fetches and accesses memory inside `d`. This is how an interference environment that
preserves the projection is eliminated from the encoder-correctness proof. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32

structure Agree (d : W → Prop) (s t : State) : Prop where
  pc : s.pc = t.pc
  nextPc : s.nextPc = t.nextPc
  gpr : s.gpr = t.gpr
  hi : s.hi = t.hi
  lo : s.lo = t.lo
  trapped : s.trapped = t.trapped
  mem : ∀ a, d a → s.mem.readByte a = t.mem.readByte a

theorem Agree.refl (d : W → Prop) (s : State) : Agree d s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Agree.symm {d : W → Prop} {s t : State} (h : Agree d s t) : Agree d t s :=
  ⟨h.pc.symm, h.nextPc.symm, h.gpr.symm, h.hi.symm, h.lo.symm, h.trapped.symm,
    fun a ha => (h.mem a ha).symm⟩

theorem Agree.trans {d : W → Prop} {s t u : State} (h₁ : Agree d s t) (h₂ : Agree d t u) :
    Agree d s u :=
  ⟨h₁.pc.trans h₂.pc, h₁.nextPc.trans h₂.nextPc, h₁.gpr.trans h₂.gpr, h₁.hi.trans h₂.hi,
    h₁.lo.trans h₂.lo, h₁.trapped.trans h₂.trapped,
    fun a ha => (h₁.mem a ha).trans (h₂.mem a ha)⟩

theorem Agree.reg {d : W → Prop} {s t : State} (h : Agree d s t) (r : Fin 32) :
    s.reg r = t.reg r := by
  simp [State.reg, h.gpr]

theorem fun2Set_eq_iff {f g : W → BitVec 8} {d : W → Prop} :
    SetSep.fun2Set (f, d) = SetSep.fun2Set (g, d) ↔ ∀ a, d a → f a = g a := by
  constructor
  · intro h a ha
    have hm : SetSep.fun2Set (f, d) (a, f a) := (SetSep.fun2SetThm f d a (f a)).2 ⟨rfl, ha⟩
    rw [h] at hm
    exact ((SetSep.fun2SetThm g d a (f a)).1 hm).1.symm
  · intro h
    funext ⟨a, b⟩
    apply propext
    rw [SetSep.fun2SetThm, SetSep.fun2SetThm]
    constructor
    · rintro ⟨rfl, ha⟩; exact ⟨(h a ha).symm, ha⟩
    · rintro ⟨rfl, ha⟩; exact ⟨h a ha, ha⟩

theorem proj_eq_iff (d : W → Prop) (s t : State) :
    mips32Proj d s = mips32Proj d t ↔ Agree d s t := by
  simp only [mips32Proj, Prod.mk.injEq, fun2Set_eq_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-! ## Memory accesses of an instruction -/

def wordAt (a : W) : List W := [a, a + 1, a + 2, a + 3]

/-- The byte addresses an instruction reads or writes, in state `s`. -/
def touched (s : State) : Insn → List W
  | .lb _ base off | .lbu _ base off | .sb _ base off => [s.reg base + sext16 off]
  | .lh _ base off | .lhu _ base off | .sh _ base off =>
    let a := s.reg base + sext16 off; [a, a + 1]
  | .lw _ base off | .ll _ base off | .sw _ base off | .sc _ base off =>
    wordAt (s.reg base + sext16 off)
  | .lwl _ base off | .lwr _ base off | .swl _ base off | .swr _ base off =>
    wordAt ((s.reg base + sext16 off) &&& ~~~(3 : W))
  | _ => []

theorem readWord_congr {m m' : Mem} {d : W → Prop} (a : W)
    (h : ∀ x, d x → m.readByte x = m'.readByte x) (ha : ∀ x ∈ wordAt a, d x) :
    m.readWord a = m'.readWord a := by
  simp only [wordAt, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ha
  rw [readWord_eq, readWord_eq, h _ ha.1, h _ ha.2.1, h _ ha.2.2.1, h _ ha.2.2.2]

theorem State.eq_withMem {s t : State} (hpc : s.pc = t.pc) (hnpc : s.nextPc = t.nextPc)
    (hgpr : s.gpr = t.gpr) (hhi : s.hi = t.hi) (hlo : s.lo = t.lo) (htr : s.trapped = t.trapped) :
    t = { s with mem := t.mem } := by
  cases s; cases t; simp_all

theorem setReg_withMem (s : State) (m : Mem) (r : Fin 32) (v : W) :
    ({ s with mem := m } : State).setReg r v = { s.setReg r v with mem := m } := by
  unfold State.setReg; split <;> rfl

theorem setReg_mem (s : State) (r : Fin 32) (v : W) : (s.setReg r v).mem = s.mem := by
  unfold State.setReg; split <;> rfl

theorem agree_withMem {d : W → Prop} (s : State) {m m' : Mem}
    (h : ∀ a, d a → m.readByte a = m'.readByte a) :
    Agree d { s with mem := m } { s with mem := m' } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, h⟩

set_option maxHeartbeats 400000 in
/-- An instruction without memory accesses does not look at the memory. -/
theorem exec_withMem (s : State) (m : Mem) (i : Insn) (hi : touched s i = []) :
    exec { s with mem := m } i = { exec s i with mem := m } := by
  cases i <;> (try simp [touched, wordAt] at hi) <;>
    simp only [exec, State.setReg, State.reg, setHiLo, hilo] <;> (try split_ifs) <;> rfl

set_option maxHeartbeats 400000 in
theorem exec_mem_nil (s : State) (i : Insn) (hi : touched s i = []) : (exec s i).mem = s.mem := by
  cases i <;> (try simp [touched, wordAt] at hi) <;>
    simp only [exec, State.setReg, State.reg, setHiLo, hilo] <;> (try split_ifs) <;> rfl

set_option maxHeartbeats 1000000 in
/-- Two states that agree on `d` execute an instruction whose accesses lie in `d` to states
that agree on `d`. -/
theorem exec_agree {d : W → Prop} {s t : State} (h : Agree d s t) (i : Insn)
    (hacc : ∀ x ∈ touched s i, d x) : Agree d (exec s i) (exec t i) := by
  rw [State.eq_withMem h.pc h.nextPc h.gpr h.hi h.lo h.trapped]
  have hmem := h.mem
  generalize t.mem = m' at hmem
  by_cases hnil : touched s i = []
  · rw [exec_withMem s m' i hnil]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a ha => by rw [exec_mem_nil s i hnil]; exact hmem a ha⟩
  have hr : ∀ x ∈ touched s i, m'.readByte x = s.mem.readByte x :=
    fun x hx => (hmem x (hacc x hx)).symm
  cases i <;> simp [touched] at hnil <;>
    simp only [touched, wordAt, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq, State.reg] at hr <;>
    simp only [exec, State.setReg, State.reg, lwl, lwr, swl, swr, Mem.readHalf, Mem.readWord,
      hr] <;>
    (try split_ifs) <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a ha => by
      simp only [Mem.writeWord, Mem.writeHalf, readByte_writeByte]
      (try split_ifs) <;> first | rfl | exact hmem a ha⟩

set_option maxHeartbeats 1000000 in
/-- An instruction whose accesses lie in `d` changes no byte outside `d`. -/
theorem exec_frame {d : W → Prop} (s : State) (i : Insn) (hacc : ∀ x ∈ touched s i, d x)
    (y : W) (hy : ¬ d y) : (exec s i).mem.readByte y = s.mem.readByte y := by
  by_cases hnil : touched s i = []
  · rw [exec_mem_nil s i hnil]
  have hne : ∀ x ∈ touched s i, y ≠ x := fun x hx hyx => hy (hyx ▸ hacc x hx)
  cases i <;> simp [touched] at hnil <;>
    simp only [touched, wordAt, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at hne <;>
    simp only [exec, lwl, lwr, swl, swr, setReg_mem, Mem.writeWord, Mem.writeHalf,
      readByte_writeByte, hne, if_false]

/-! ## Fetching and the asm-level step -/

/-- One fetch-and-execute stays inside `d`: the instruction word and the instruction's
accesses. -/
def StepSafe (d : W → Prop) (s : State) : Prop :=
  (∀ x ∈ wordAt s.pc, d x) ∧ ∀ i, decode (s.mem.readWord s.pc) = some i → ∀ x ∈ touched s i, d x

theorem fetchExec_agree {d : W → Prop} {s t : State} (h : Agree d s t) (hs : StepSafe d s) :
    Agree d (fetchExec s) (fetchExec t) := by
  have hw : s.mem.readWord s.pc = t.mem.readWord t.pc := by
    rw [← h.pc]; exact readWord_congr s.pc h.mem hs.1
  unfold fetchExec
  rw [← hw]
  cases hd : decode (s.mem.readWord s.pc) with
  | none => exact ⟨h.pc, h.nextPc, h.gpr, h.hi, h.lo, rfl, h.mem⟩
  | some i => exact exec_agree h i (hs.2 i hd)

theorem fetchExec_frame {d : W → Prop} (s : State) (hs : StepSafe d s) (y : W) (hy : ¬ d y) :
    (fetchExec s).mem.readByte y = s.mem.readByte y := by
  unfold fetchExec
  cases hd : decode (s.mem.readWord s.pc) with
  | none => rfl
  | some i => exact exec_frame s i (hs.2 i hd) y hy

/-- `mips32Next` stays inside `d`. -/
def NextSafe (d : W → Prop) (s : State) : Prop :=
  s.trapped = false → StepSafe d s ∧
    ((fetchExec s).trapped = false → (fetchExec s).nextPc ≠ (fetchExec s).pc + 4 →
      StepSafe d (fetchExec s))

theorem next_agree {d : W → Prop} {s t : State} (h : Agree d s t) (hs : NextSafe d s) :
    Agree d (mips32Next s) (mips32Next t) := by
  unfold mips32Next
  rw [← h.trapped]
  by_cases ht : s.trapped = true
  · simp only [ht, ↓reduceIte]; exact h
  have ht' : s.trapped = false := by simpa using ht
  obtain ⟨h1, h2⟩ := hs ht'
  have ha := fetchExec_agree h h1
  simp only [ht, Bool.false_eq_true, ↓reduceIte]
  rw [← ha.trapped, ← ha.nextPc, ← ha.pc]
  split
  · exact ha
  · rename_i hc
    simp only [not_or, Bool.not_eq_true] at hc
    exact fetchExec_agree ha (h2 hc.1 hc.2)

theorem next_frame {d : W → Prop} (s : State) (hs : NextSafe d s) (y : W) (hy : ¬ d y) :
    (mips32Next s).mem.readByte y = s.mem.readByte y := by
  unfold mips32Next
  by_cases ht : s.trapped = true
  · simp [ht]
  have ht' : s.trapped = false := by simpa using ht
  obtain ⟨h1, h2⟩ := hs ht'
  simp only [ht, Bool.false_eq_true, ↓reduceIte]
  split
  · exact fetchExec_frame s h1 y hy
  · rename_i hc
    simp only [not_or, Bool.not_eq_true] at hc
    rw [fetchExec_frame _ (h2 hc.1 hc.2) y hy, fetchExec_frame s h1 y hy]

end Flapjack.Mips32.TargetProof
