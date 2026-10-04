import Flapjack.Compiler.Backend.LabFilter.Proofs.InstructionCases

/-! Complete native control-case family of original filter_correct669:
Jump, JumpReg, LocValue, JumpCmp and Call, including all error paths.
The whole evaluator-case assembly and semantic lift remain open. -/

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Native missing-target consequence of the source relation. Flapjack
infrastructure assembling original control cases, with no separate HOL original. -/
private theorem relatedGetPcNone {width : Nat} [NeZero width] {C F : Type}
    (label : Lab) (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hrel : stateRel s t) (h : getPcValue label s = none) : getPcValue label t = none := by
  rcases hrel with ⟨⟨_, rfl, _⟩, _⟩
  cases label with
  | lab n1 n2 => exact locToPcEqNone n1 n2 t.code h

/-- Native target-PC witness derived from the source relation. Flapjack
infrastructure assembling original control cases, with no separate HOL original. -/
private theorem relatedGetPcSome {width : Nat} [NeZero width] {C F : Type}
    (label : Lab) (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (pc : Nat) (hrel : stateRel s t) (h : getPcValue label s = some pc) :
    ∃ originalPc, getPcValue label t = some originalPc ∧ adjustPc originalPc t.code = pc := by
  rcases hrel with ⟨⟨_, rfl, _⟩, _⟩
  cases label with
  | lab n1 n2 => exact locToPcEqSome n1 n2 t.code pc h

/-- Jump successor relation, derived rather than supplied as a simulation premise.
Flapjack infrastructure for the original control cases, with no separate HOL original. -/
private theorem relatedJumpSuccessor {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (pc originalPc : Nat)
    (hrel : stateRel s t) (hpc : adjustPc originalPc t.code = pc) :
    stateRel (updPc pc (decClock s)) (updPc originalPc (decClock t)) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp [updPc, decClock, hpc]
  · exact hcompile
  · exact hfailed

/-- Original labelled-Jump branch with its actual guarded recursive induction
hypothesis. Missing targets and all result constructors are retained.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectJump {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.jump label) position bytes len))
    (ih : s1.clock ≠ 0 → ∀ pc, getPcValue label s1 = some pc →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (updPc pc (decClock s1)) = (result, final) →
      stateRel (updPc pc (decClock s1)) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (updPc pc (decClock s1)).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.jump label) position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases hp : getPcValue label s1 with
  | none =>
    have htarget := relatedGetPcNone label s1 t1 hrel hp
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hp] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      have hlookup : getPcValue label {t1 with pc := t1.pc + count} = none := by
        cases label; simpa only [getPcValue] using htarget
      simp only [hlookup]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
  | some pc =>
    obtain ⟨originalPc, htarget, hpc⟩ := relatedGetPcSome label s1 t1 pc hrel hp
    have hn := relatedJumpSuccessor s1 t1 pc originalPc hrel hpc
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hp] at he
    obtain ⟨extra, t2, hrun, hffi⟩ := ih hc pc hp _ res s2 he hn hn.2
    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
    refine ⟨extra + count, t2, ?_, hffi⟩
    simp only [Nat.add_zero] at hskipRun
    rw [hsclock, ← Nat.add_assoc, hskipRun]
    conv => lhs; rw [evaluate]
    have hnonzero : t1.clock + extra ≠ 0 := by omega
    simp only [hnonzero, ↓reduceIte, asmFetch, halign]
    have hlookup : getPcValue label {t1 with pc := t1.pc + count, clock := t1.clock + extra} = some originalPc := by
      cases label; simpa only [getPcValue] using htarget
    simp only [hlookup]
    have hstep : updPc originalPc (decClock {t1 with pc := t1.pc + count, clock := t1.clock + extra}) =
        {updPc originalPc (decClock t1) with clock := (updPc pc (decClock s1)).clock + extra} := by
      simp only [updPc, decClock, hsclock]
      congr 1
      omega
    rw [hstep]
    exact hrun

/-- Original JumpReg location-valued branch with its actual guarded recursive induction
hypothesis. Missing targets and all result constructors are retained.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectJumpRegLoc {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (register sectionId labelId : Nat) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg register)) bytes len))
    (hreg : s1.regs register = .loc sectionId labelId)
    (ih : s1.clock ≠ 0 → ∀ pc, locToPc sectionId labelId s1.code = some pc →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (updPc pc (decClock s1)) = (result, final) →
      stateRel (updPc pc (decClock s1)) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (updPc pc (decClock s1)).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.asm (.asmi (.jumpReg register)) bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have htreg : t1.regs register = .loc sectionId labelId := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs] using hreg
  cases hp : locToPc sectionId labelId s1.code with
  | none =>
    have htarget := relatedGetPcNone (.lab sectionId labelId) s1 t1 hrel hp
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hreg, hp] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign, htreg]
      have hlookup : locToPc sectionId labelId t1.code = none := htarget
      simp only [hlookup]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
  | some pc =>
    obtain ⟨originalPc, htarget, hpc⟩ := relatedGetPcSome (.lab sectionId labelId) s1 t1 pc hrel hp
    have hn := relatedJumpSuccessor s1 t1 pc originalPc hrel hpc
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hreg, hp] at he
    obtain ⟨extra, t2, hrun, hffi⟩ := ih hc pc hp _ res s2 he hn hn.2
    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
    refine ⟨extra + count, t2, ?_, hffi⟩
    simp only [Nat.add_zero] at hskipRun
    rw [hsclock, ← Nat.add_assoc, hskipRun]
    conv => lhs; rw [evaluate]
    have hnonzero : t1.clock + extra ≠ 0 := by omega
    simp only [hnonzero, ↓reduceIte, asmFetch, halign, htreg]
    have hlookup : locToPc sectionId labelId t1.code = some originalPc := htarget
    simp only [hlookup]
    have hstep : updPc originalPc (decClock {t1 with pc := t1.pc + count, clock := t1.clock + extra}) =
        {updPc originalPc (decClock t1) with clock := (updPc pc (decClock s1)).clock + extra} := by
      simp only [updPc, decClock, hsclock]
      congr 1
      omega
    rw [hstep]
    exact hrun

/-- Original JumpReg word-valued operand failure branch. No source successor
is invoked; the original existential target execution and FFI result are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectJumpRegWord {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (register : Nat) (value : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg register)) bytes len))
    (hreg : s1.regs register = .word value) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.asm (.asmi (.jumpReg register)) bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have htreg : t1.regs register = .word value := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs] using hreg
  have he := heval
  conv at he => lhs; rw [evaluate]
  simp only [hc, ↓reduceIte, hfetch, hreg] at he
  cases he
  have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
  refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
  · simp only [Nat.add_zero] at hrun
    rw [hsclock, hrun]
    conv => lhs; rw [evaluate]
    simp only [htclock, ↓reduceIte, asmFetch, halign, htreg]
  · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]

/-- Register-write successor relation for the native LocValue branch. Flapjack
infrastructure; the PC correspondence is derived from the actual skipped run. -/
private theorem relatedLocValueSuccessor {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (count register : Nat)
    (label : Lab) (hrel : stateRel s t) (hskips : allSkips t.pc t.code count) :
    stateRel (incPc (decClock (updReg register (labToLoc label) s)))
      (incPc (decClock (updReg register (labToLoc label) {t with pc := t.pc + count}))) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  have hadj := adjustPcAllSkips count t.pc t.code hskips
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp [incPc, decClock, updReg, ← hadj]
  · exact hcompile
  · exact hfailed

/-- Original LocValue branch with its actual guarded recursive induction
hypothesis. Missing targets and all result constructors are retained.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (register : Nat) (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.locValue register label) position bytes len))
    (ih : s1.clock ≠ 0 → getPcValue label s1 ≠ none →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (incPc (decClock (updReg register (labToLoc label) s1))) = (result, final) →
      stateRel (incPc (decClock (updReg register (labToLoc label) s1))) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (incPc (decClock (updReg register (labToLoc label) s1))).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.locValue register label) position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases hp : getPcValue label s1 with
  | none =>
    have htarget := relatedGetPcNone label s1 t1 hrel hp
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hp] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      have hlookup : getPcValue label {t1 with pc := t1.pc + count} = none := by
        cases label; simpa only [getPcValue] using htarget
      simp [hlookup]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
  | some pc =>
    obtain ⟨originalPc, htarget, _⟩ := relatedGetPcSome label s1 t1 pc hrel hp
    have hn := relatedLocValueSuccessor s1 t1 count register label hrel hskips
    have hmissing : (some pc : Option Nat) ≠ none := by intro h; cases h
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hp, hmissing] at he
    have hpresent : getPcValue label s1 ≠ none := by
      intro h
      rw [hp] at h
      cases h
    obtain ⟨extra, t2, hrun, hffi⟩ := ih hc hpresent _ res s2 he hn hn.2
    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
    refine ⟨extra + count, t2, ?_, hffi⟩
    simp only [Nat.add_zero] at hskipRun
    rw [hsclock, ← Nat.add_assoc, hskipRun]
    conv => lhs; rw [evaluate]
    have hnonzero : t1.clock + extra ≠ 0 := by omega
    simp only [hnonzero, ↓reduceIte, asmFetch, halign]
    have hlookup : getPcValue label {t1 with pc := t1.pc + count, clock := t1.clock + extra} = some originalPc := by
      cases label; simpa only [getPcValue] using htarget
    simp [hlookup]
    have hstep : incPc (decClock (updReg register (labToLoc label) {t1 with pc := t1.pc + count, clock := t1.clock + extra})) =
        {incPc (decClock (updReg register (labToLoc label) {t1 with pc := t1.pc + count})) with
          clock := (incPc (decClock (updReg register (labToLoc label) s1))).clock + extra} := by
      simp only [incPc, decClock, updReg, hsclock]
      congr 1
      omega
    rw [hstep]
    exact hrun


/-- Return-label equality from the actual skipped run. Flapjack infrastructure
for the native Call branch, with no separate HOL original. -/
private theorem relatedRetLoc {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (count : Nat)
    (hrel : stateRel s t) (hskips : allSkips t.pc t.code count) :
    getRetLoc (resultWidth := width) {t with pc := t.pc + count} =
      getRetLoc (resultWidth := width) s := by
  rcases hrel with ⟨⟨_, rfl, _⟩, _⟩
  exact getLabAfterAdjust t.pc t.code count hskips

/-- Call successor relation, including the link register write. Flapjack
infrastructure; the target label/PC correspondence is derived before use. -/
private theorem relatedCallSuccessor {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (pc originalPc : Nat)
    (location : WordLocW width) (hrel : stateRel s t)
    (hpc : adjustPc originalPc t.code = pc) :
    stateRel (updPc pc (decClock (updReg s.linkReg location s)))
      (updPc originalPc (decClock (updReg t.linkReg location t))) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp [updPc, decClock, updReg, hpc]
  · exact hcompile
  · exact hfailed

/-- Original Call branch with its actual guarded recursive induction
hypothesis. Missing targets and all result constructors are retained.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.call label) position bytes len))
    (ih : s1.clock ≠ 0 → ∀ pc (location : WordLocW width), getPcValue label s1 = some pc →
      getRetLoc s1 = some location →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (updPc pc (decClock (updReg s1.linkReg location s1))) = (result, final) →
      stateRel (updPc pc (decClock (updReg s1.linkReg location s1))) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (updPc pc (decClock (updReg s1.linkReg location s1))).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.call label) position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases hp : getPcValue label s1 with
  | none =>
    have htarget := relatedGetPcNone label s1 t1 hrel hp
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hp] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      have hlookup : getPcValue label {t1 with pc := t1.pc + count} = none := by
        cases label; simpa only [getPcValue] using htarget
      simp only [hlookup]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
  | some pc =>
    obtain ⟨originalPc, htarget, hpc⟩ := relatedGetPcSome label s1 t1 pc hrel hp
    have hret := relatedRetLoc s1 t1 count hrel hskips
    have hlink : s1.linkReg = t1.linkReg := by
      rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
    cases hr : getRetLoc (resultWidth := width) s1 with
    | none =>
      have htargetRet : getRetLoc (resultWidth := width) {t1 with pc := t1.pc + count} = none := hret.trans hr
      have he := heval
      conv at he => lhs; rw [evaluate]
      simp only [hc, ↓reduceIte, hfetch, hp, hr] at he
      cases he
      have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
      refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
      · simp only [Nat.add_zero] at hrun
        rw [hsclock, hrun]
        conv => lhs; rw [evaluate]
        simp only [htclock, ↓reduceIte, asmFetch, halign]
        have hlookup : getPcValue label {t1 with pc := t1.pc + count} = some originalPc := by
          cases label; simpa only [getPcValue] using htarget
        simp only [hlookup, htargetRet]
      · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
        rw [hs]
    | some location =>
      have hn := relatedCallSuccessor s1 t1 pc originalPc location hrel hpc
      have he := heval
      conv at he => lhs; rw [evaluate]
      simp only [hc, ↓reduceIte, hfetch, hp, hr] at he
      obtain ⟨extra, t2, hrun, hffi⟩ := ih hc pc location hp hr _ res s2 he hn hn.2
      have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
      refine ⟨extra + count, t2, ?_, hffi⟩
      simp only [Nat.add_zero] at hskipRun
      rw [hsclock, ← Nat.add_assoc, hskipRun]
      conv => lhs; rw [evaluate]
      have hnonzero : t1.clock + extra ≠ 0 := by omega
      simp only [hnonzero, ↓reduceIte, asmFetch, halign]
      have hlookup : getPcValue label {t1 with pc := t1.pc + count, clock := t1.clock + extra} = some originalPc := by
        cases label; simpa only [getPcValue] using htarget
      have htargetRet : getRetLoc (resultWidth := width) {t1 with pc := t1.pc + count, clock := t1.clock + extra} = some location := by
        simpa only [getRetLoc] using hret.trans hr
      simp only [hlookup, htargetRet]
      have hstep : updPc originalPc (decClock (updReg t1.linkReg location {t1 with pc := t1.pc + count, clock := t1.clock + extra})) =
          {updPc originalPc (decClock (updReg t1.linkReg location t1)) with
            clock := (updPc pc (decClock (updReg s1.linkReg location s1))).clock + extra} := by
        simp only [updPc, decClock, updReg, hsclock]
        congr 1
        omega
      rw [hstep]
      exact hrun

/-- Pure operand comparison ignores the fields changed by filtering. Flapjack
infrastructure for the native JumpCmp cases, with no separate HOL declaration. -/
private theorem relatedWordCmp {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (comparison : HolCmp) (register : Nat) (operand : HolRegImm width) (hrel : stateRel s t) :
    wordSemWordCmp comparison (s.regs register) (regImm operand s) =
      wordSemWordCmp comparison (t.regs register) (regImm operand t) := by
  rcases hrel with ⟨⟨_, rfl, _⟩, _⟩
  cases operand <;> rfl

/-- Fall-through successor relation, derived from the actual skipped run.
Flapjack infrastructure for the native JumpCmp case, with no separate HOL original. -/
private theorem relatedIncSuccessor {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (count : Nat)
    (hrel : stateRel s t) (hskips : allSkips t.pc t.code count) :
    stateRel (incPc (decClock s)) (incPc (decClock {t with pc := t.pc + count})) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  have hadj := adjustPcAllSkips count t.pc t.code hskips
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp [incPc, decClock, ← hadj]
  · exact hcompile
  · exact hfailed

/-- Original JumpCmp taken branch with its actual guarded recursive induction
hypothesis. Missing targets and all result constructors are retained.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectJumpCmpTrue {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (comparison : HolCmp) (register : Nat) (operand : HolRegImm width)
    (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp comparison register operand label) position bytes len))
    (hcmp : wordSemWordCmp comparison (s1.regs register) (regImm operand s1) = some true)
    (ih : s1.clock ≠ 0 → ∀ pc, getPcValue label s1 = some pc →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (updPc pc (decClock s1)) = (result, final) →
      stateRel (updPc pc (decClock s1)) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (updPc pc (decClock s1)).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.jumpCmp comparison register operand label) position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have htcmp := (relatedWordCmp s1 t1 comparison register operand hrel).symm.trans hcmp
  cases hp : getPcValue label s1 with
  | none =>
    have htarget := relatedGetPcNone label s1 t1 hrel hp
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hcmp, hp] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      have hcompare : wordSemWordCmp comparison ({t1 with pc := t1.pc + count}.regs register)
          (regImm operand {t1 with pc := t1.pc + count}) = some true := by
        cases operand <;> simpa only [regImm] using htcmp
      simp only [hcompare]
      have hlookup : getPcValue label {t1 with pc := t1.pc + count} = none := by
        cases label; simpa only [getPcValue] using htarget
      simp only [hlookup]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
  | some pc =>
    obtain ⟨originalPc, htarget, hpc⟩ := relatedGetPcSome label s1 t1 pc hrel hp
    have hn := relatedJumpSuccessor s1 t1 pc originalPc hrel hpc
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hcmp, hp] at he
    obtain ⟨extra, t2, hrun, hffi⟩ := ih hc pc hp _ res s2 he hn hn.2
    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
    refine ⟨extra + count, t2, ?_, hffi⟩
    simp only [Nat.add_zero] at hskipRun
    rw [hsclock, ← Nat.add_assoc, hskipRun]
    conv => lhs; rw [evaluate]
    have hnonzero : t1.clock + extra ≠ 0 := by omega
    simp only [hnonzero, ↓reduceIte, asmFetch, halign]
    have hcompare : wordSemWordCmp comparison ({t1 with pc := t1.pc + count, clock := t1.clock + extra}.regs register)
        (regImm operand {t1 with pc := t1.pc + count, clock := t1.clock + extra}) = some true := by
      cases operand <;> simpa only [regImm] using htcmp
    simp only [hcompare]
    have hlookup : getPcValue label {t1 with pc := t1.pc + count, clock := t1.clock + extra} = some originalPc := by
      cases label; simpa only [getPcValue] using htarget
    simp only [hlookup]
    have hstep : updPc originalPc (decClock {t1 with pc := t1.pc + count, clock := t1.clock + extra}) =
        {updPc originalPc (decClock t1) with clock := (updPc pc (decClock s1)).clock + extra} := by
      simp only [updPc, decClock, hsclock]
      congr 1
      omega
    rw [hstep]
    exact hrun


/-- Original JumpCmp comparison failure branch. No source successor
is invoked; the original existential target execution and FFI result are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectJumpCmpNone {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (comparison : HolCmp) (register : Nat) (operand : HolRegImm width)
    (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp comparison register operand label) position bytes len))
    (hcmp : wordSemWordCmp comparison (s1.regs register) (regImm operand s1) = none) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.jumpCmp comparison register operand label) position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have htcmp := (relatedWordCmp s1 t1 comparison register operand hrel).symm.trans hcmp
  have he := heval
  conv at he => lhs; rw [evaluate]
  simp only [hc, ↓reduceIte, hfetch, hcmp] at he
  cases he
  have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
  refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
  · simp only [Nat.add_zero] at hrun
    rw [hsclock, hrun]
    conv => lhs; rw [evaluate]
    simp only [htclock, ↓reduceIte, asmFetch, halign]
    have hcompare : wordSemWordCmp comparison ({t1 with pc := t1.pc + count}.regs register)
        (regImm operand {t1 with pc := t1.pc + count}) = none := by
      cases operand <;> simpa only [regImm] using htcmp
    simp only [hcompare]
  · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]


/-- Original JumpCmp fall-through branch. The only induction hypothesis concerns
its actual native source successor; no label lookup or success premise is added.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectJumpCmpFalse {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (comparison : HolCmp) (register : Nat) (operand : HolRegImm width)
    (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp comparison register operand label) position bytes len))
    (hcmp : wordSemWordCmp comparison (s1.regs register) (regImm operand s1) = some false)
    (ih : s1.clock ≠ 0 → ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (incPc (decClock s1)) = (result, final) →
      stateRel (incPc (decClock s1)) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (incPc (decClock s1)).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.jumpCmp comparison register operand label) position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have htcmp := (relatedWordCmp s1 t1 comparison register operand hrel).symm.trans hcmp
  have hn := relatedIncSuccessor s1 t1 count hrel hskips
  have he := heval
  conv at he => lhs; rw [evaluate]
  simp only [hc, ↓reduceIte, hfetch, hcmp] at he
  obtain ⟨extra, t2, hrun, hffi⟩ := ih hc _ res s2 he hn hn.2
  have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
  refine ⟨extra + count, t2, ?_, hffi⟩
  simp only [Nat.add_zero] at hskipRun
  rw [hsclock, ← Nat.add_assoc, hskipRun]
  conv => lhs; rw [evaluate]
  have hnonzero : t1.clock + extra ≠ 0 := by omega
  simp only [hnonzero, ↓reduceIte, asmFetch, halign]
  have hcompare : wordSemWordCmp comparison ({t1 with pc := t1.pc + count, clock := t1.clock + extra}.regs register)
      (regImm operand {t1 with pc := t1.pc + count, clock := t1.clock + extra}) = some false := by
    cases operand <;> simpa only [regImm] using htcmp
  simp only [hcompare]
  have hstep : incPc (decClock {t1 with pc := t1.pc + count, clock := t1.clock + extra}) =
      {incPc (decClock {t1 with pc := t1.pc + count}) with clock := (incPc (decClock s1)).clock + extra} := by
    simp only [incPc, decClock, hsclock]
    congr 1
    omega
  rw [hstep]
  exact hrun

end Flapjack.Compiler.Backend.LabFilter.Proofs
