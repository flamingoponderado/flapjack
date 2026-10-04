import Flapjack.Compiler.Backend.LabFilter.Proofs.CallFfiCases
import Flapjack.Compiler.Backend.LabFilter.Map

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Flapjack infrastructure naming the literal successful native Install record
update. The original evaluator has no separately named declaration for it. -/
private def installReturnState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F)
    (program : LabProgHOL width) (installedSection pc : Nat)
    (buffer : WordSemBuffer width 8) : Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with
    pc := pc
    codeBuffer := buffer
    code := state.code ++ program
    ccRegs := holShiftSeq 1 state.ccRegs
    ccFpRegs := holShiftSeq 1 state.ccFpRegs
    regs := fun r => if r = state.ptrReg then .loc installedSection 0
      else getRegValue (state.ccRegs 0 r) (state.regs r) WordLocW.word
    fpRegs := fun r => state.ccFpRegs 0 r
    compileOracle := holShiftSeq 1 state.compileOracle
    clock := state.clock - 1 }

/-- Derive the entire native installed successor relation from the original
compiler/oracle relation, actual locator, and map/append laws. Flapjack proof
infrastructure for original Install; no separate HOL declaration names it. -/
private theorem relatedInstallReturn {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (program : LabProgHOL width) (installedSection sectionId labelId pc originalPc : Nat)
    (buffer : WordSemBuffer width 8) (hrel : stateRel s t)
    (hlookup : locToPc sectionId labelId t.code = some originalPc)
    (hpc : adjustPc originalPc t.code = pc) :
    stateRel (installReturnState s (filterSkip program) installedSection pc buffer)
      (installReturnState t program installedSection originalPc buffer) := by
  have hadj : adjustPc originalPc (t.code ++ program) = pc :=
    (locToPcAdjustPcAppend sectionId labelId t.code originalPc program hlookup).symm.trans hpc
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp only [installReturnState, filterSkipAppend, holShiftSeq, hadj]
    rfl
  · exact hcompile
  · exact hfailed

/-- Full original Install evaluator constructor. Compiler/oracle, buffer,
locator, nonempty-program and byte/config guards remain actual source choices;
the only IH simulates the literal successful installed source successor.
The IH includes the original evaluator's nonzero source-clock path guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterCorrectInstall {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (position : BitVec width) (encoded : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm .install position encoded len))
    (ih : s1.clock ≠ 0 → ∀ (program : LabProgHOL width) (installedSection pc : Nat) (buffer : WordSemBuffer width 8),
      (∃ (start finish : BitVec width) (sectionId labelId : Nat) (bytes compiledBytes : List (BitVec 8))
          (configuration nextConfiguration : C),
        s1.regs s1.ptrReg = .word start ∧ s1.regs s1.lenReg = .word finish ∧
        s1.regs s1.linkReg = .loc sectionId labelId ∧
        wordSemBufferFlush s1.codeBuffer start finish = some (bytes, buffer) ∧
        locToPc sectionId labelId s1.code = some pc ∧
        s1.compileOracle 0 = (configuration, program) ∧
        s1.compile configuration program = some (compiledBytes, nextConfiguration) ∧
        (∃ lines rest, program = ⟨installedSection, lines⟩ :: rest) ∧
        bytes = compiledBytes ∧ (holShiftSeq 1 s1.compileOracle 0).1 = nextConfiguration) →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (installReturnState s1 program installedSection pc buffer) = (result, final) →
      stateRel (installReturnState s1 program installedSection pc buffer) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (installReturnState s1 program installedSection pc buffer).clock + extra} =
        (result, t2) ∧ final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  classical
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hrelation := hrel
  obtain ⟨⟨sourceCompile, hs, hcompile⟩, _⟩ := hrel
  have hsclock : s1.clock = t1.clock := by rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm .install position encoded len) := by
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases hr0 : t1.regs t1.ptrReg with
  | loc sectionId labelId =>
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch] at he
    simp only [hs, hr0] at he
    cases he
    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
    simp only [Nat.add_zero] at hrun
    rw [hsclock, hrun]
    conv => lhs; rw [evaluate]
    simp only [htclock, ↓reduceIte, asmFetch, halign, hr0]
  | word start =>
    cases hr1 : t1.regs t1.lenReg with
    | loc sectionId labelId =>
      have he := heval
      conv at he => lhs; rw [evaluate]
      simp only [hc, ↓reduceIte, hfetch] at he
      simp only [hs, hr0, hr1] at he
      cases he
      have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
      refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
      simp only [Nat.add_zero] at hrun
      rw [hsclock, hrun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1]
    | word finish =>
      cases hr2 : t1.regs t1.linkReg with
      | word value =>
        have he := heval
        conv at he => lhs; rw [evaluate]
        simp only [hc, ↓reduceIte, hfetch] at he
        simp only [hs, hr0, hr1, hr2] at he
        cases he
        have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
        refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
        simp only [Nat.add_zero] at hrun
        rw [hsclock, hrun]
        conv => lhs; rw [evaluate]
        simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2]
      | loc sectionId labelId =>
        cases hflush : wordSemBufferFlush t1.codeBuffer start finish with
        | none =>
          have he := heval
          conv at he => lhs; rw [evaluate]
          simp only [hc, ↓reduceIte, hfetch] at he
          simp only [hs, hr0, hr1, hr2, hflush] at he
          cases he
          have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
          refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
          simp only [Nat.add_zero] at hrun
          rw [hsclock, hrun]
          conv => lhs; rw [evaluate]
          simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hflush]
        | some pair =>
          rcases pair with ⟨bytes, buffer⟩
          cases hsourceLoc : locToPc sectionId labelId (filterSkip t1.code) with
          | none =>
            have htargetLoc := locToPcEqNone sectionId labelId t1.code hsourceLoc
            have he := heval
            conv at he => lhs; rw [evaluate]
            simp only [hc, ↓reduceIte, hfetch] at he
            simp only [hs, hr0, hr1, hr2, hflush, hsourceLoc] at he
            cases he
            have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
            refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
            simp only [Nat.add_zero] at hrun
            rw [hsclock, hrun]
            conv => lhs; rw [evaluate]
            simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hflush, htargetLoc]
          | some pc =>
            obtain ⟨originalPc, htargetLoc, hpc⟩ := locToPcEqSome sectionId labelId t1.code pc hsourceLoc
            cases ho : t1.compileOracle 0 with
            | mk configuration program =>
              cases hcomp : sourceCompile configuration (filterSkip program) with
              | none =>
                have he := heval
                conv at he => lhs; rw [evaluate]
                simp only [hc, ↓reduceIte, hfetch] at he
                simp only [hs, hr0, hr1, hr2, hflush, hsourceLoc, ho, hcomp] at he
                cases he
                have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
                refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
                simp only [Nat.add_zero] at hrun
                rw [hsclock, hrun]
                conv => lhs; rw [evaluate]
                simp only [htclock, ↓reduceIte, asmFetch, halign, hcompile, hr0, hr1, hr2, hflush, htargetLoc, ho, hcomp]
              | some pair =>
                rcases pair with ⟨compiledBytes, nextConfiguration⟩
                cases program with
                | nil =>
                  have he := heval
                  conv at he => lhs; rw [evaluate]
                  simp only [hc, ↓reduceIte, hfetch] at he
                  simp only [hs, hr0, hr1, hr2, hflush, hsourceLoc, ho, hcomp] at he
                  simp only [filterSkip] at he
                  cases he
                  have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
                  refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
                  simp only [Nat.add_zero] at hrun
                  rw [hsclock, hrun]
                  conv => lhs; rw [evaluate]
                  simp only [htclock, ↓reduceIte, asmFetch, halign, hcompile, hr0, hr1, hr2, hflush, htargetLoc, ho, hcomp]
                | cons sect rest =>
                  rcases sect with ⟨installedSection, lines⟩
                  by_cases hv : bytes = compiledBytes ∧ (t1.compileOracle 1).1 = nextConfiguration
                  ·
                    have hn := relatedInstallReturn s1 t1 (⟨installedSection, lines⟩ :: rest) installedSection sectionId labelId
                      pc originalPc buffer hrelation htargetLoc hpc
                    have he : evaluate (installReturnState s1 (filterSkip (⟨installedSection, lines⟩ :: rest)) installedSection pc buffer) = (res, s2) := by
                      have he := heval
                      conv at he => lhs; rw [evaluate]
                      simp only [hc, ↓reduceIte, hfetch] at he
                      simp only [hs, hr0, hr1, hr2, hflush, hsourceLoc, ho, hcomp] at he
                      simp only [filterSkip, holShiftSeq] at he
                      change (if bytes = compiledBytes ∧ (holShiftSeq 1 t1.compileOracle 0).1 = nextConfiguration then _ else _) = _ at he
                      rw [if_pos (by simpa only [holShiftSeq] using hv)] at he
                      simpa only [hs, filterSkip, holShiftSeq, installReturnState] using he
                    have hpath : ∃ (start finish : BitVec width) (sectionId labelId : Nat) (bytes compiledBytes : List (BitVec 8))
                        (configuration nextConfiguration : C),
                      s1.regs s1.ptrReg = .word start ∧ s1.regs s1.lenReg = .word finish ∧
                      s1.regs s1.linkReg = .loc sectionId labelId ∧
                      wordSemBufferFlush s1.codeBuffer start finish = some (bytes, buffer) ∧
                      locToPc sectionId labelId s1.code = some pc ∧
                      s1.compileOracle 0 = (configuration, filterSkip (⟨installedSection, lines⟩ :: rest)) ∧
                      s1.compile configuration (filterSkip (⟨installedSection, lines⟩ :: rest)) = some (compiledBytes, nextConfiguration) ∧
                      (∃ sourceLines sourceRest, filterSkip (⟨installedSection, lines⟩ :: rest) = ⟨installedSection, sourceLines⟩ :: sourceRest) ∧
                      bytes = compiledBytes ∧ (holShiftSeq 1 s1.compileOracle 0).1 = nextConfiguration := by
                      refine ⟨start, finish, sectionId, labelId, bytes, compiledBytes, configuration, nextConfiguration, ?_⟩
                      refine ⟨by simpa only [hs] using hr0, by simpa only [hs] using hr1,
                        by simpa only [hs] using hr2, by simpa only [hs] using hflush,
                        by simpa only [hs] using hsourceLoc, ?_, by simpa only [hs] using hcomp, ?_, hv.1, ?_⟩
                      · simp only [hs, ho]
                      · exact ⟨lines.filter notSkip, filterSkip rest, rfl⟩
                      · simpa only [hs, holShiftSeq] using hv.2
                    obtain ⟨extra, t2, hrun, hffi⟩ := ih hc (filterSkip (⟨installedSection, lines⟩ :: rest)) installedSection pc buffer
                      hpath _ res s2 he hn hn.2
                    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
                    refine ⟨extra + count, t2, ?_, hffi⟩
                    simp only [Nat.add_zero] at hskipRun
                    rw [hsclock, ← Nat.add_assoc, hskipRun]
                    conv => lhs; rw [evaluate]
                    have hnonzero : t1.clock + extra ≠ 0 := by omega
                    simp only [hnonzero, ↓reduceIte, asmFetch, halign, hcompile, hr0, hr1, hr2, hflush, htargetLoc, ho, hcomp]
                    simp only [holShiftSeq]
                    change (if bytes = compiledBytes ∧ (holShiftSeq 1 t1.compileOracle 0).1 = nextConfiguration then _ else _) = _
                    rw [if_pos (by simpa only [holShiftSeq] using hv)]
                    rw [← hcompile]
                    change evaluate (installReturnState {t1 with pc := t1.pc + count, clock := t1.clock + extra}
                      (⟨installedSection, lines⟩ :: rest) installedSection originalPc buffer) = (res, t2)
                    have hstep : installReturnState {t1 with pc := t1.pc + count, clock := t1.clock + extra}
                        (⟨installedSection, lines⟩ :: rest) installedSection originalPc buffer =
                        {installReturnState t1 (⟨installedSection, lines⟩ :: rest) installedSection originalPc buffer with
                          clock := (installReturnState s1 (filterSkip (⟨installedSection, lines⟩ :: rest)) installedSection pc buffer).clock + extra} := by
                      simp only [installReturnState, hsclock]
                      congr 1
                      omega
                    rw [hstep]
                    exact hrun
                  ·
                    have he := heval
                    conv at he => lhs; rw [evaluate]
                    simp only [hc, ↓reduceIte, hfetch] at he
                    simp only [hs, hr0, hr1, hr2, hflush, hsourceLoc, ho, hcomp] at he
                    simp only [filterSkip, holShiftSeq] at he
                    change (if bytes = compiledBytes ∧ (holShiftSeq 1 t1.compileOracle 0).1 = nextConfiguration then _ else _) = _ at he
                    rw [if_neg (by simpa only [holShiftSeq] using hv)] at he
                    cases he
                    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
                    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
                    simp only [Nat.add_zero] at hrun
                    rw [hsclock, hrun]
                    conv => lhs; rw [evaluate]
                    simp only [htclock, ↓reduceIte, asmFetch, halign, hcompile, hr0, hr1, hr2, hflush, htargetLoc, ho, hcomp]
                    simp only [holShiftSeq]
                    change (if bytes = compiledBytes ∧ (holShiftSeq 1 t1.compileOracle 0).1 = nextConfiguration then _ else _) = _
                    rw [if_neg (by simpa only [holShiftSeq] using hv)]


end Flapjack.Compiler.Backend.LabFilter.Proofs
