import Flapjack.Compiler.Backend.LabFilter.Proofs.Simulation

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Literal source filtering record update at a selected PC. This is Flapjack
proof infrastructure, not a separately named HOL declaration. -/
private def filterAt {width : Nat} [NeZero width] {C F : Type}
    (sourceCompile : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (pc : Nat) (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  {t with
    pc := pc
    code := filterSkip t.code
    compile := sourceCompile
    compileOracle := fun n => ((t.compileOracle n).1, filterSkip (t.compileOracle n).2)}

/-- All ordinary native instructions commute with the four source-filter frame
updates, including failures and FP operations. Flapjack infrastructure assembling
the original instruction cases; there is no separate HOL declaration. -/
private theorem asmInstFilterAt {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width)
    (sourceCompile : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (pc : Nat) (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmInst instruction (filterAt sourceCompile pc t) =
      filterAt sourceCompile pc (asmInst instruction t) := by
  cases instruction with
  | skip => rfl
  | const => rfl
  | arith operation =>
    cases operation <;> simp only [asmInst, arithUpd, filterAt, regImm]
    all_goals repeat' first
      | rfl
      | simp_all [binopUpd, updReg, assertState]
      | split
  | mem operator register address =>
    cases operator <;> simp only [asmInst, memOp, memLoad, memStore,
      memLoad32, memStore32, memLoadByte, memStoreByte, filterAt, addrValue]
    all_goals repeat' first
      | rfl
      | simp_all [updReg, updMem, assertState]
      | split
  | fp operation =>
    cases operation <;> simp only [asmInst, fpUpd, filterAt, readFpReg]
    all_goals repeat' first
      | rfl
      | simp_all [updFpReg, updReg, assertState]
      | split

/-- PC/clock record update for proof bookkeeping, with no separate HOL original. -/
private def retime {width : Nat} [NeZero width] {C F : Type} (pc clock : Nat)
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F := {t with pc := pc, clock := clock}

/-- All instruction updates ignore PC and clock. Flapjack proof infrastructure,
not a separately named HOL declaration; failures are included. -/
private theorem asmInstRetime {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (pc clock : Nat)
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmInst instruction (retime pc clock t) = retime pc clock (asmInst instruction t) := by
  cases instruction with
  | skip => rfl
  | const => rfl
  | arith operation =>
    cases operation <;> simp only [asmInst, arithUpd, retime, regImm]
    all_goals repeat' first
      | rfl
      | simp_all [binopUpd, updReg, assertState]
      | split
  | mem operator register address =>
    cases operator <;> simp only [asmInst, memOp, memLoad, memStore,
      memLoad32, memStore32, memLoadByte, memStoreByte, retime, addrValue]
    all_goals repeat' first
      | rfl
      | simp_all [updReg, updMem, assertState]
      | split
  | fp operation =>
    cases operation <;> simp only [asmInst, fpUpd, retime, readFpReg]
    all_goals repeat' first
      | rfl
      | simp_all [updFpReg, updReg, assertState]
      | split

/-- Native compiler metadata is unchanged by ordinary instructions. Flapjack
infrastructure needed to assemble the source relation; no separate HOL original. -/
private theorem asmInstCompilerFrame {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (asmInst instruction t).compile = t.compile ∧
      (asmInst instruction t).compileOracle = t.compileOracle := by
  cases instruction with
  | skip => exact ⟨rfl, rfl⟩
  | const => exact ⟨rfl, rfl⟩
  | arith operation =>
    cases operation <;> simp only [asmInst, arithUpd, regImm]
    all_goals repeat' first
      | rfl
      | simp_all [binopUpd, updReg, assertState]
      | split
  | mem operator register address =>
    cases operator <;> simp only [asmInst, memOp, memLoad, memStore,
      memLoad32, memStore32, memLoadByte, memStoreByte, addrValue]
    all_goals repeat' first
      | rfl
      | simp_all [updReg, updMem, assertState]
      | split
  | fp operation =>
    cases operation <;> simp only [asmInst, fpUpd, readFpReg]
    all_goals repeat' first
      | rfl
      | simp_all [updFpReg, updReg, assertState]
      | split

/-- Successor relation derived from native instruction commutation and skipped-run
PC adjustment. Flapjack infrastructure for the original recursive cases. -/
private theorem stateRelInstSuccessor {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (count : Nat) (hrel : stateRel s t) (hskips : allSkips t.pc t.code count)
    (hok : (asmInst instruction s).failed = false) :
    stateRel (incPc (decClock (asmInst instruction s)))
      (incPc (decClock (asmInst instruction (retime (t.pc + count) t.clock t)))) := by
  rcases hrel with ⟨⟨sourceCompile, rfl, hcompile⟩, _⟩
  change (asmInst instruction (filterAt sourceCompile (adjustPc t.pc t.code) t)).failed = false at hok
  rw [asmInstFilterAt] at hok
  change stateRel (incPc (decClock (asmInst instruction (filterAt sourceCompile (adjustPc t.pc t.code) t)))) _
  rw [asmInstFilterAt, asmInstRetime]
  have hcode := (asmInstConsts instruction t).2.1
  have hclock := (asmInstConsts instruction t).2.2.1
  have hmeta := asmInstCompilerFrame instruction t
  have hadj := adjustPcAllSkips count t.pc t.code hskips
  unfold stateRel
  refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
  · simp only [incPc, decClock, filterAt, retime]
    simp only [hcode, hclock, hmeta.2, ← hadj]
  · simpa only [incPc, decClock, retime, hmeta.1] using hcompile
  · simpa only [incPc, decClock, retime, filterAt] using hok

/-- Original ordinary-instruction branch. The only induction hypothesis is the
full original simulation for the actual recursive source successor. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrectInstruction {width : Nat} [NeZero width] {C F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (instruction : HolInst width) (bytes : List (BitVec 8)) (len : Nat)
    (heval : evaluate s1 = (res, s2)) (hrel : stateRel s1 t1)
    (hfailed : t1.failed = false)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.inst instruction)) bytes len))
    (ih : ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
        (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
      (asmInst instruction s1).failed = false →
      evaluate (incPc (decClock (asmInst instruction s1))) = (result, final) →
      stateRel (incPc (decClock (asmInst instruction s1))) target → target.failed = false →
      ∃ extra t2, evaluate {target with
        clock := (incPc (decClock (asmInst instruction s1))).clock + extra} = (result, t2) ∧
        final.ffi = t2.ffi) :
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  by_cases hc : s1.clock = 0
  · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
  have hsclock : s1.clock = t1.clock := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    rw [hs]
  have htclock : t1.clock ≠ 0 := by omega
  have hf : asmFetchAux (adjustPc t1.pc t1.code) (filterSkip t1.code) =
      some (.asm (.asmi (.inst instruction)) bytes len) := by
    rcases hrel with ⟨⟨_, hs, _⟩, _⟩
    simpa only [hs, asmFetch] using hfetch
  obtain ⟨count, halign, hskips⟩ := asmFetchAuxEq2 t1.pc t1.code _ hf
  have hinst : (asmInst instruction s1).failed = (asmInst instruction t1).failed := by
    rcases hrel with ⟨⟨sourceCompile, hs, _⟩, _⟩
    rw [hs]
    change (asmInst instruction (filterAt sourceCompile (adjustPc t1.pc t1.code) t1)).failed = _
    rw [asmInstFilterAt]
    rfl
  by_cases hok : (asmInst instruction s1).failed = false
  · have hn : stateRel (incPc (decClock (asmInst instruction s1)))
        (incPc (decClock (asmInst instruction (retime (t1.pc + count) t1.clock t1)))) :=
      stateRelInstSuccessor instruction s1 t1 count hrel hskips hok
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hok, Bool.false_eq_true] at he
    obtain ⟨extra, t2, hrun, hffi⟩ := ih _ res s2 hok he hn hn.2
    have hsourceClock : (incPc (decClock (asmInst instruction s1))).clock = t1.clock - 1 := by
      simp only [incPc, decClock, (asmInstConsts instruction s1).2.2.1, hsclock]
    have hstep : incPc (decClock (asmInst instruction (retime (t1.pc + count) (t1.clock + extra) t1))) =
        {incPc (decClock (asmInst instruction (retime (t1.pc + count) t1.clock t1))) with
          clock := (incPc (decClock (asmInst instruction s1))).clock + extra} := by
      rw [hsourceClock, asmInstRetime, asmInstRetime]
      simp only [incPc, decClock, retime]
      congr 1
      omega
    have hskipRun := allSkipsEvaluate count {t1 with clock := t1.clock + extra} ⟨hskips, hfailed⟩ 0
    refine ⟨extra + count, t2, ?_, hffi⟩
    simp only [Nat.add_zero] at hskipRun
    rw [hsclock, ← Nat.add_assoc, hskipRun]
    conv => lhs; rw [evaluate]
    have hnonzero : t1.clock + extra ≠ 0 := by omega
    simp only [hnonzero, ↓reduceIte, asmFetch, halign]
    change (if (asmInst instruction (retime (t1.pc + count) (t1.clock + extra) t1)).failed then _ else _) = _
    have htargetok : (asmInst instruction (retime (t1.pc + count) (t1.clock + extra) t1)).failed = false := by
      rw [asmInstRetime]
      simpa only [retime, hinst] using hok
    simp only [htargetok, Bool.false_eq_true, ↓reduceIte]
    change evaluate (incPc (decClock (asmInst instruction (retime (t1.pc + count) (t1.clock + extra) t1)))) = _
    rw [hstep]
    exact hrun
  · have hbad : (asmInst instruction s1).failed = true := by
      cases hb : (asmInst instruction s1).failed with
      | false => exact (hok hb).elim
      | true => rfl
    have he := heval
    conv at he => lhs; rw [evaluate]
    simp only [hc, ↓reduceIte, hfetch, hbad] at he
    cases he
    have hskipRun := allSkipsEvaluate count t1 ⟨hskips, hfailed⟩ 0
    refine ⟨count, {t1 with pc := t1.pc + count}, ?_, ?_⟩
    · simp only [Nat.add_zero] at hskipRun
      rw [hsclock, hskipRun]
      conv => lhs; rw [evaluate]
      simp only [htclock, ↓reduceIte, asmFetch, halign]
      change (if (asmInst instruction (retime (t1.pc + count) t1.clock t1)).failed then _ else _) = _
      rw [asmInstRetime]
      simp only [retime, ← hinst, hbad, ↓reduceIte]
    · rcases hrel with ⟨⟨_, hs, _⟩, _⟩
      rw [hs]

end Flapjack.Compiler.Backend.LabFilter.Proofs
