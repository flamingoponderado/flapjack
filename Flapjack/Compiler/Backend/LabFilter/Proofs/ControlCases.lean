import Flapjack.Compiler.Backend.LabFilter.Proofs.InstructionCases

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
hypothesis. Missing targets and all result constructors are retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectJump {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (label : Lab) (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.jump label) position bytes len))
    (ih : ∀ pc, getPcValue label s1 = some pc →
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
    obtain ⟨extra, t2, hrun, hffi⟩ := ih pc hp _ res s2 he hn hn.2
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
hypothesis. Missing targets and all result constructors are retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectJumpRegLoc {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (register sectionId labelId : Nat) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg register)) bytes len))
    (hreg : s1.regs register = .loc sectionId labelId)
    (ih : ∀ pc, locToPc sectionId labelId s1.code = some pc →
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
    obtain ⟨extra, t2, hrun, hffi⟩ := ih pc hp _ res s2 he hn hn.2
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
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
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

end Flapjack.Compiler.Backend.LabFilter.Proofs
