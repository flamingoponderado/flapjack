import Flapjack.Compiler.Backend.LabFilter.Proofs.ControlCases

/-! Native buffer-write and terminal constructor cases of original
filter_correct669. Full evaluator assembly and semantic lift remain open. -/

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Original Label/default Error constructor branch, retaining all source simulation hypotheses and
outcomes. The skipped-run count and actual target execution are derived. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectLabel {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (sectionId labelId len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.label sectionId labelId len)) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.label sectionId labelId len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have he := heval
  conv at he => lhs; rw [evaluate]
  simp only [hc, ↓reduceIte, hfetch] at he

  cases he
  have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
  refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
  · simp only [Nat.add_zero] at hrun
    rw [hsclock, hrun]
    conv => lhs; rw [evaluate]
    simp only [htclock, ↓reduceIte, asmFetch, halign]
  · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]

/-- Original Halt constructor, including zero/nonzero Word and Loc error branch, retaining all source simulation hypotheses and
outcomes. The skipped-run count and actual target execution are derived. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectHalt {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (position : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm .halt position bytes len)) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm .halt position bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have he := heval
  conv at he => lhs; rw [evaluate]
  simp only [hc, ↓reduceIte, hfetch] at he
  have hregs : s1.regs s1.ptrReg = t1.regs t1.ptrReg := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  rw [hregs] at he
  cases hr : t1.regs t1.ptrReg with
  | loc sectionId labelId =>
    simp only [hr] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign, hr]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]

  | word value =>
    simp only [hr] at he
    split at he <;> rename_i hz <;> cases he
    all_goals
      have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
      refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
      · simp only [Nat.add_zero] at hrun
        rw [hsclock, hrun]
        conv => lhs; rw [evaluate]
        simp only [htclock, ↓reduceIte, asmFetch, halign, hr, hz]
      · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
        rw [hs]

/-- Native code-buffer update successor relation. Flapjack infrastructure for
the original CBW case, with no separately named HOL original. -/
private theorem relatedBufferSuccessor {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (buffer : WordSemBuffer width 8) (count : Nat) (hrel : stateRel s t)
    (hskips : allSkips t.pc t.code count) :
    stateRel (incPc (decClock {s with codeBuffer := buffer}))
      (incPc (decClock {t with pc := t.pc + count, codeBuffer := buffer})) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  have hadj := adjustPcAllSkips count t.pc t.code hskips
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp only [incPc, decClock, ← hadj]
  · exact hcompile
  · exact hfailed

/-- Original CBW constructor, retaining invalid operands, failed writes, and the
actual successful byte-buffer update. The only induction hypothesis is the
original simulation of that guarded source successor; target execution and its
successor relation are derived.
The IH includes the original evaluator's nonzero source-clock path guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (r1 r2 : Nat) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.cbw r1 r2) bytes len))
    (ih : s1.clock ≠ 0 → ∀ (address value : BitVec width) (buffer : WordSemBuffer width 8),
      s1.regs r1 = .word address → s1.regs r2 = .word value →
      wordSemBufferWrite s1.codeBuffer address (value.setWidth 8) = some buffer →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (incPc (decClock {s1 with codeBuffer := buffer})) = (result, final) →
      stateRel (incPc (decClock {s1 with codeBuffer := buffer})) target → target.failed = false →
      ∃ extra t2, evaluate {target with
        clock := (incPc (decClock {s1 with codeBuffer := buffer})).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.asm (.cbw r1 r2) bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have hregs1 : s1.regs r1 = t1.regs r1 := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have hregs2 : s1.regs r2 = t1.regs r2 := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have hbuffer : s1.codeBuffer = t1.codeBuffer := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  cases hr1 : s1.regs r1 with
  | loc sectionId labelId =>
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hr1] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign, ← hregs1, ← hregs2, ← hbuffer, hr1]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]
  | word address =>
    cases hr2 : s1.regs r2 with
    | loc sectionId labelId =>
      have he := heval
      conv at he => lhs; rw [evaluate]
      simp only [hc, ↓reduceIte, hfetch, hr1, hr2] at he
      cases he
      have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
      refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
      · simp only [Nat.add_zero] at hrun
        rw [hsclock, hrun]
        conv => lhs; rw [evaluate]
        simp only [htclock, ↓reduceIte, asmFetch, halign, ← hregs1, ← hregs2, ← hbuffer, hr1, hr2]
      · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
        rw [hs]
    | word value =>
      cases hw : wordSemBufferWrite s1.codeBuffer address (value.setWidth 8) with
      | none =>
        have he := heval
        conv at he => lhs; rw [evaluate]
        simp only [hc, ↓reduceIte, hfetch, hr1, hr2, hw] at he
        cases he
        have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
        refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
        · simp only [Nat.add_zero] at hrun
          rw [hsclock, hrun]
          conv => lhs; rw [evaluate]
          simp only [htclock, ↓reduceIte, asmFetch, halign, ← hregs1, ← hregs2, ← hbuffer, hr1, hr2, hw]
        · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
          rw [hs]
      | some buffer =>
        have hn := relatedBufferSuccessor s1 t1 buffer count hrel hskips
        have he := heval
        conv at he => lhs; rw [evaluate]
        simp only [hc, ↓reduceIte, hfetch, hr1, hr2, hw] at he
        obtain ⟨extra, t2, hrun, hffi⟩ := ih hc address value buffer hr1 hr2 hw _ res s2 he hn hn.2
        have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
        refine ⟨extra + count, t2, ?_, hffi⟩
        simp only [Nat.add_zero] at hskipRun
        rw [hsclock, ← Nat.add_assoc, hskipRun]
        conv => lhs; rw [evaluate]
        have hnonzero : t1.clock + extra ≠ 0 := by omega
        simp only [hnonzero, ↓reduceIte, asmFetch, halign, ← hregs1, ← hregs2, hr1, hr2, ← hbuffer, hw]
        have hstep : incPc (decClock {t1 with pc := t1.pc + count, clock := t1.clock + extra, codeBuffer := buffer}) =
            {incPc (decClock {t1 with pc := t1.pc + count, codeBuffer := buffer}) with
              clock := (incPc (decClock {s1 with codeBuffer := buffer})).clock + extra} := by
          simp only [incPc, decClock, hsclock]
          congr 1
          omega
        rw [hstep]
        exact hrun

end Flapjack.Compiler.Backend.LabFilter.Proofs
