import Flapjack.Compiler.Backend.LabFilter.Proofs.SharedMemoryCases

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Flapjack infrastructure naming the literal native CallFFI returning record
update for the original evaluator case. There is no separate HOL declaration. -/
private def callFfiReturnState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F)
    (function : Flapjack.Basis.Pure.MlString.MlString) (start2 : BitVec width)
    (pc : Nat) (ffi : HolFfiState F) (returned : List (BitVec 8)) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with
    memory := writeBytearrayExact start2 returned state.memory state.memDomain state.be
    ffi := ffi
    ioRegs := holShiftSeq 1 state.ioRegs
    ioFpRegs := holShiftSeq 1 state.ioFpRegs
    regs := fun r => getRegValue (state.ioRegs 0 (.extCall function) r) (state.regs r) WordLocW.word
    fpRegs := fun r => state.ioFpRegs 0 r
    pc := pc
    clock := state.clock - 1 }

/-- Literal FFI-return memory/register/IO update preserves the original full
relation at the derived target locator. Flapjack infrastructure, no HOL original. -/
private theorem relatedCallFfiReturn {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (function : Flapjack.Basis.Pure.MlString.MlString) (start2 : BitVec width)
    (pc originalPc : Nat) (ffi : HolFfiState F) (returned : List (BitVec 8))
    (hrel : stateRel s t) (hpc : adjustPc originalPc t.code = pc) :
    stateRel (callFfiReturnState s function start2 pc ffi returned)
      (callFfiReturnState t function start2 originalPc ffi returned) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, hfailed⟩
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp only [callFfiReturnState, hpc]
  · exact hcompile
  · exact hfailed

/-- Full original CallFFI evaluator constructor. Every register/read/locator
failure and FFI final/return outcome is retained. The only IH is the original
simulation for the actual returned source successor, guarded by its source path.
The IH includes the original evaluator's nonzero source-clock path guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectCallFfi {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (position : BitVec width) (encoded : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.labAsm (.callFFI function) position encoded len))
    (ih : s1.clock ≠ 0 → ∀ (start2 : BitVec width) (pc : Nat) (ffi : HolFfiState F) (returned : List (BitVec 8)),
      (∃ (length start length2 : BitVec width) (sectionId labelId : Nat)
          (configuration bytes : List (BitVec 8)),
        s1.regs s1.lenReg = .word length ∧ s1.regs s1.ptrReg = .word start ∧
        s1.regs s1.len2Reg = .word length2 ∧ s1.regs s1.ptr2Reg = .word start2 ∧
        s1.regs s1.linkReg = .loc sectionId labelId ∧
        readBytearrayWordHOL start length.toNat (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some configuration ∧
        readBytearrayWordHOL start2 length2.toNat (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes ∧
        locToPc sectionId labelId s1.code = some pc ∧
        callFFIHOL s1.ffi (.extCall function) configuration bytes = .ret ffi returned) →
      ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate (callFfiReturnState s1 function start2 pc ffi returned) = (result, final) →
      stateRel (callFfiReturnState s1 function start2 pc ffi returned) target → target.failed = false →
      ∃ extra t2, evaluate {target with clock := (callFfiReturnState s1 function start2 pc ffi returned).clock + extra} =
        (result, t2) ∧ final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hrelation := hrel
  obtain ⟨⟨sourceCompile, hs, _⟩, _⟩ := hrel
  have hsclock : s1.clock = t1.clock := by rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.labAsm (.callFFI function) position encoded len) := by
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  cases hr0 : t1.regs t1.lenReg with
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
  | word length =>
    cases hr1 : t1.regs t1.ptrReg with
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
    | word start =>
      cases hr2 : t1.regs t1.len2Reg with
      | loc sectionId labelId =>
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
      | word length2 =>
        cases hr3 : t1.regs t1.ptr2Reg with
        | loc sectionId labelId =>
          have he := heval
          conv at he => lhs; rw [evaluate]
          simp only [hc, ↓reduceIte, hfetch] at he
          simp only [hs, hr0, hr1, hr2, hr3] at he
          cases he
          have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
          refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
          simp only [Nat.add_zero] at hrun
          rw [hsclock, hrun]
          conv => lhs; rw [evaluate]
          simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3]
        | word start2 =>
          cases hr4 : t1.regs t1.linkReg with
          | word value =>
            have he := heval
            conv at he => lhs; rw [evaluate]
            simp only [hc, ↓reduceIte, hfetch] at he
            simp only [hs, hr0, hr1, hr2, hr3, hr4] at he
            cases he
            have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
            refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
            simp only [Nat.add_zero] at hrun
            rw [hsclock, hrun]
            conv => lhs; rw [evaluate]
            simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3, hr4]
          | loc sectionId labelId =>
            cases hread1 : readBytearrayWordHOL start length.toNat (memLoadByteAuxExact t1.memory t1.memDomain t1.be) with
            | none =>
              have he := heval
              conv at he => lhs; rw [evaluate]
              simp only [hc, ↓reduceIte, hfetch] at he
              simp only [hs, hr0, hr1, hr2, hr3, hr4, hread1] at he
              cases he
              have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
              refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
              simp only [Nat.add_zero] at hrun
              rw [hsclock, hrun]
              conv => lhs; rw [evaluate]
              simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3, hr4, hread1]
            | some configuration =>
              cases hread2 : readBytearrayWordHOL start2 length2.toNat (memLoadByteAuxExact t1.memory t1.memDomain t1.be) with
              | none =>
                have he := heval
                conv at he => lhs; rw [evaluate]
                simp only [hc, ↓reduceIte, hfetch] at he
                simp only [hs, hr0, hr1, hr2, hr3, hr4, hread1, hread2] at he
                cases he
                have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
                refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
                simp only [Nat.add_zero] at hrun
                rw [hsclock, hrun]
                conv => lhs; rw [evaluate]
                simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3, hr4, hread1, hread2]
              | some bytes =>
                cases hsourceLoc : locToPc sectionId labelId (filterSkip t1.code) with
                | none =>
                  have htargetLoc := locToPcEqNone sectionId labelId t1.code hsourceLoc
                  have he := heval
                  conv at he => lhs; rw [evaluate]
                  simp only [hc, ↓reduceIte, hfetch] at he
                  simp only [hs, hr0, hr1, hr2, hr3, hr4, hread1, hread2, hsourceLoc] at he
                  cases he
                  have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
                  refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
                  simp only [Nat.add_zero] at hrun
                  rw [hsclock, hrun]
                  conv => lhs; rw [evaluate]
                  simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3, hr4, hread1, hread2, htargetLoc]
                | some pc =>
                  obtain ⟨originalPc, htargetLoc, hpc⟩ := locToPcEqSome sectionId labelId t1.code pc hsourceLoc
                  cases hffi : callFFIHOL t1.ffi (.extCall function) configuration bytes with
                  | final outcome =>
                    have he := heval
                    conv at he => lhs; rw [evaluate]
                    simp only [hc, ↓reduceIte, hfetch] at he
                    simp only [hs, hr0, hr1, hr2, hr3, hr4, hread1, hread2, hsourceLoc, hffi] at he
                    cases he
                    have hrun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
                    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, rfl⟩
                    simp only [Nat.add_zero] at hrun
                    rw [hsclock, hrun]
                    conv => lhs; rw [evaluate]
                    simp only [htclock, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3, hr4, hread1, hread2, htargetLoc, hffi]
                  | ret ffi returned =>
                    have hn := relatedCallFfiReturn s1 t1 function start2 pc originalPc ffi returned hrelation hpc
                    have he : evaluate (callFfiReturnState s1 function start2 pc ffi returned) = (res, s2) := by
                      have he := heval
                      conv at he => lhs; rw [evaluate]
                      simp only [hc, ↓reduceIte, hfetch] at he
                      simpa only [hs, hr0, hr1, hr2, hr3, hr4, hread1, hread2, hsourceLoc, hffi, callFfiReturnState] using he
                    have hpath : ∃ (length start length2 : BitVec width) (sectionId labelId : Nat)
                        (configuration bytes : List (BitVec 8)),
                      s1.regs s1.lenReg = .word length ∧ s1.regs s1.ptrReg = .word start ∧
                      s1.regs s1.len2Reg = .word length2 ∧ s1.regs s1.ptr2Reg = .word start2 ∧
                      s1.regs s1.linkReg = .loc sectionId labelId ∧
                      readBytearrayWordHOL start length.toNat (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some configuration ∧
                      readBytearrayWordHOL start2 length2.toNat (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes ∧
                      locToPc sectionId labelId s1.code = some pc ∧
                      callFFIHOL s1.ffi (.extCall function) configuration bytes = .ret ffi returned := by
                      refine ⟨length, start, length2, sectionId, labelId, configuration, bytes, ?_⟩
                      simpa only [hs] using And.intro hr0 (And.intro hr1 (And.intro hr2 (And.intro hr3 (And.intro hr4 (And.intro hread1 (And.intro hread2 (And.intro hsourceLoc hffi)))))))
                    obtain ⟨extra, t2, hrun, hresultFfi⟩ := ih hc start2 pc ffi returned hpath _ res s2 he hn hn.2
                    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
                    refine ⟨extra + count, t2, ?_, hresultFfi⟩
                    simp only [Nat.add_zero] at hskipRun
                    rw [hsclock, ← Nat.add_assoc, hskipRun]
                    conv => lhs; rw [evaluate]
                    have hnonzero : t1.clock + extra ≠ 0 := by omega
                    simp only [hnonzero, ↓reduceIte, asmFetch, halign, hr0, hr1, hr2, hr3, hr4, hread1, hread2, htargetLoc, hffi]
                    change evaluate (callFfiReturnState {t1 with pc := t1.pc + count, clock := t1.clock + extra}
                      function start2 originalPc ffi returned) = (res, t2)
                    have hstep : callFfiReturnState {t1 with pc := t1.pc + count, clock := t1.clock + extra}
                        function start2 originalPc ffi returned =
                        {callFfiReturnState t1 function start2 originalPc ffi returned with
                          clock := (callFfiReturnState s1 function start2 pc ffi returned).clock + extra} := by
                      simp only [callFfiReturnState, hsclock]
                      congr 1
                      omega
                    rw [hstep]
                    exact hrun

end Flapjack.Compiler.Backend.LabFilter.Proofs
