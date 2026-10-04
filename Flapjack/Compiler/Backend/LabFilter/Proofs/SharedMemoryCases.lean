import Flapjack.Compiler.Backend.LabFilter.Proofs.BufferTerminalCases

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Updating both IO sequences preserves the derived native filter relation.
Flapjack infrastructure for the original returning case; no separate HOL original. -/
private theorem relatedShiftIo {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (hrel : stateRel s t) :
    stateRel {s with ioRegs := holShiftSeq 1 s.ioRegs, ioFpRegs := holShiftSeq 1 s.ioFpRegs}
      {t with ioRegs := holShiftSeq 1 t.ioRegs, ioFpRegs := holShiftSeq 1 t.ioFpRegs} := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  exact ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩

/-- Full original SharedMem evaluator constructor: NONE, final FFI and returning
FFI outcomes. Only the actual returning source successor supplies an induction
hypothesis; target primitive/execution, clock and successor relation are derived.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectSharedMemory {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.shareMem operator register address) bytes len))
    (ih : s1.clock ≠ 0 → ∀ (ffi : HolFfiState F) (returned : List (BitVec 8))
        (next : Flapjack.Compiler.Backend.LabSem.State width C F),
      shareMemOp operator register address s1 = some (.ret ffi returned, next) →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate {next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs} =
        (result, final) →
      stateRel {next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs} target →
      target.failed = false →
      ∃ extra t2, evaluate {target with clock := next.clock + extra} = (result, t2) ∧ final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  obtain ⟨⟨sourceCompile, hs, hcompile⟩, _⟩ := hrel
  have hsclock : s1.clock = t1.clock := by rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.asm (.shareMem operator register address) bytes len) := by
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases hp : shareMemOp operator register address s1 with
  | none =>
    have htarget := shareMemOpNoneFilterCorrect t1 count operator register address sourceCompile
      (fun n => ((t1.compileOracle n).1, filterSkip (t1.compileOracle n).2)) ⟨hskips, by simpa only [hs] using hp⟩
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch] at he
    rw [hp] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      have hlookup : shareMemOp operator register address {t1 with pc := t1.pc + count} = none := by
        simpa only [Nat.add_comm count t1.pc] using htarget
      rw [hlookup]
    · rw [hs]
  | some pair =>
    rcases pair with ⟨outcome, next⟩
    cases outcome with
    | final outcome =>
      obtain ⟨targetNext, htarget, hffi⟩ := shareMemOpFfiFinalFilterCorrect t1 count operator register address
        sourceCompile outcome next ⟨hskips, htclock, hcompile, hfailed, by simpa only [hs] using hp⟩
      have he := heval
      conv at he => lhs; rw [evaluate]
      simp only [hc, ↓reduceIte, hfetch] at he
      rw [hp] at he
      cases he
      have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
      refine ⟨count, targetNext, ?_, hffi⟩
      simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      have hlookup : shareMemOp operator register address {t1 with pc := t1.pc + count} =
          some (.final outcome, targetNext) := by
        simpa only [Nat.add_comm count t1.pc] using htarget
      rw [hlookup]
    | ret ffi returned =>
      obtain ⟨targetNext, htarget⟩ := shareMemOpFfiReturnFilterCorrect t1 count operator register address
        sourceCompile ffi returned next ⟨hskips, htclock, hcompile, hfailed, by simpa only [hs] using hp⟩
      have hn := relatedShiftIo next targetNext (htarget 0).2.1
      have he := heval
      conv at he => lhs; rw [evaluate]
      simp only [hc, ↓reduceIte, hfetch] at he
      rw [hp] at he
      obtain ⟨extra, t2, hrun, hffi⟩ := ih hc ffi returned next hp _ res s2 he hn hn.2
      have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
      refine ⟨extra + count, t2, ?_, hffi⟩
      simp only [Nat.add_zero] at hskipRun
      rw [hsclock, ← Nat.add_assoc, hskipRun]
      conv => lhs; rw [evaluate]
      have hnonzero : t1.clock + extra ≠ 0 := by omega
      simp only [hnonzero, ↓reduceIte, asmFetch, halign]
      have hlookup : shareMemOp operator register address {t1 with pc := t1.pc + count, clock := t1.clock + extra} =
          some (.ret ffi returned, {targetNext with clock := extra + targetNext.clock}) := by
        simpa only [Nat.add_comm count t1.pc, Nat.add_comm extra t1.clock] using (htarget extra).2.2.2.2
      rw [hlookup]
      have hclock : next.clock = targetNext.clock := by
        rcases (htarget 0).2.1 with ⟨⟨_, hnext, _⟩, _⟩
        rw [hnext]
      have hstep :
          {{targetNext with clock := extra + targetNext.clock} with
            ioRegs := holShiftSeq 1 targetNext.ioRegs, ioFpRegs := holShiftSeq 1 targetNext.ioFpRegs} =
          {{targetNext with ioRegs := holShiftSeq 1 targetNext.ioRegs, ioFpRegs := holShiftSeq 1 targetNext.ioFpRegs}
            with clock := next.clock + extra} := by
        simp only [hclock, Nat.add_comm extra targetNext.clock]
      change evaluate {{targetNext with clock := extra + targetNext.clock} with
        ioRegs := holShiftSeq 1 targetNext.ioRegs, ioFpRegs := holShiftSeq 1 targetNext.ioFpRegs} = (res, t2)
      rw [hstep]
      exact hrun

end Flapjack.Compiler.Backend.LabFilter.Proofs
