import Flapjack.Compiler.Backend.LabFilter.Proofs.ReturnLabels
import Flapjack.Compiler.Backend.LabFilter.Proofs.SharedMemory

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Original evaluate-induction clock-zero case. All simulation hypotheses and
existential execution/FFI conclusions are retained; full assembly remains open. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectClockZero {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (_hfailed : t1.failed = false) (hclock : s1.clock = 0) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  have he : (.timeOut, s1) = (res, s2) := by
    simpa only [evaluate, hclock, ↓reduceIte] using heval
  cases he
  obtain ⟨⟨sourceCompile, hs, _⟩, _⟩ := hrel
  refine ⟨0, {t1 with clock := 0}, ?_, ?_⟩
  · simp [hclock, evaluate]
  · subst s1
    rfl

/-- Original absent-fetch branch, preserving all original simulation hypotheses
and outcomes. The actual skipped-run count is derived from native fetch alignment. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectAbsentFetch {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false) (hfetch : asmFetch s1 = none) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have he : (.error, s1) = (res, s2) := by
    simpa only [evaluate, hc, ↓reduceIte, hfetch] using heval
  cases he
  obtain ⟨⟨sourceCompile, hs, _⟩, _⟩ := hrel
  subst s1
  have htclock : t1.clock ≠ 0 := hc
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) = none := by
    simpa only [asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code none hf
  have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
  refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
  simp only [Nat.add_zero] at hrun
  rw [hrun]
  conv => lhs; rw [evaluate]
  simp [htclock, asmFetch, halign]

end Flapjack.Compiler.Backend.LabFilter.Proofs
