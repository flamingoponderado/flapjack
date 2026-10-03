import Flapjack.Compiler.Backend.LabFilter.Proofs.PcAdjustment
import Flapjack.Compiler.Backend.LabProps.ClockSupport

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Full original NONE clause, retaining its allSkips premise and arbitrary compiler/oracle binders. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "share_mem_op_NONE_filter_correct"
  (words_as_type_indexed_bitvec)]
theorem shareMemOpNoneFilterCorrect {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) (count : Nat)
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (sourceCompile : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (sourceOracle : Nat → C × LabProgHOL width) :
    allSkips t.pc t.code count ∧
      shareMemOp operator register address
        { t with
          pc := adjustPc t.pc t.code
          code := filterSkip t.code
          compile := sourceCompile
          compileOracle := sourceOracle } = none →
    shareMemOp operator register address { t with pc := count + t.pc } = none := by
  rintro ⟨_, hs⟩
  cases operator <;> cases address <;>
    simp only [shareMemOp, shareMemLoad, shareMemStore, addrValue] at *
  all_goals repeat' first | split at hs | simp_all

/-- Full original final-outcome clause. The actual original-PC state is derived;
all source guards and arbitrary configuration/FFI carriers are retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "share_mem_op_FFI_final_filter_correct"
  (words_as_type_indexed_bitvec)]
theorem shareMemOpFfiFinalFilterCorrect {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) (count : Nat)
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (sourceCompile : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (outcome : HolFinalEvent) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    allSkips t.pc t.code count ∧ t.clock ≠ 0 ∧
      t.compile = (fun config program => sourceCompile config (filterSkip program)) ∧
      t.failed = false ∧
      shareMemOp operator register address
        { t with
          pc := adjustPc t.pc t.code
          code := filterSkip t.code
          compile := sourceCompile
          compileOracle := (fun n => ((t.compileOracle n).1, filterSkip (t.compileOracle n).2)) } =
        some (.final outcome, s) →
    ∃ s2 : Flapjack.Compiler.Backend.LabSem.State width C F,
      shareMemOp operator register address { t with pc := count + t.pc } =
        some (.final outcome, s2) ∧ s.ffi = s2.ffi := by
  rintro ⟨_, _, _, _, hs⟩
  refine ⟨{ t with pc := count + t.pc }, ?_⟩
  cases operator <;> cases address <;>
    simp only [shareMemOp, shareMemLoad, shareMemStore, addrValue] at *
  all_goals repeat' first | split at hs | simp_all
  all_goals exact (congrArg (fun st : Flapjack.Compiler.Backend.LabSem.State width C F => st.ffi) hs.2).symm

/-- Full original returning shared-memory filter simulation. The existential
poststate, entire state relation, nonfailed facts and arbitrary clock extension
are derived over the actual native primitive; every source guard is retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "share_mem_op_FFI_return_filter_correct"
  (words_as_type_indexed_bitvec)]
theorem shareMemOpFfiReturnFilterCorrect {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) (count : Nat)
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (sourceCompile : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    allSkips t.pc t.code count ∧ t.clock ≠ 0 ∧
      t.compile = (fun config program => sourceCompile config (filterSkip program)) ∧
      t.failed = false ∧
      shareMemOp operator register address
        { t with
          pc := adjustPc t.pc t.code
          code := filterSkip t.code
          compile := sourceCompile
          compileOracle := (fun n => ((t.compileOracle n).1, filterSkip (t.compileOracle n).2)) } =
        some (.ret ffi bytes, s) →
    ∃ s2 : Flapjack.Compiler.Backend.LabSem.State width C F, ∀ extra,
      shareMemOp operator register address { t with pc := count + t.pc } =
        some (.ret ffi bytes, s2) ∧
      stateRel s s2 ∧ s.failed = false ∧ s2.failed = false ∧
      shareMemOp operator register address { t with pc := count + t.pc, clock := extra + t.clock } =
        some (.ret ffi bytes, { s2 with clock := extra + s2.clock }) := by
  rintro ⟨hskips, hclock, hcompile, hfailed, hs⟩
  have hadj : adjustPc (count + (t.pc + 1)) t.code = adjustPc t.pc t.code + 1 := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (adjustPcAllSkips count t.pc t.code hskips).symm
  have hret : ∃ s2 : Flapjack.Compiler.Backend.LabSem.State width C F,
      shareMemOp operator register address { t with pc := count + t.pc } =
        some (.ret ffi bytes, s2) ∧ stateRel s s2 ∧ s.failed = false ∧ s2.failed = false := by
    cases operator <;> cases address <;>
      simp only [shareMemOp, shareMemLoad, shareMemStore, addrValue] at hs
    all_goals repeat' first | split at hs | simp_all [incPc, decClock]
    all_goals rcases hs with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals simp_all [shareMemOp, shareMemLoad, shareMemStore, addrValue, incPc, decClock]
    all_goals unfold stateRel
    all_goals refine ⟨⟨sourceCompile, ?_, ?_⟩, ?_⟩
    all_goals simp_all [Nat.add_assoc]
  obtain ⟨s2, hbase, hrel, hsfailed, htfailed⟩ := hret
  refine ⟨s2, fun extra => ⟨hbase, hrel, hsfailed, htfailed, ?_⟩⟩
  -- The literal final event instantiates only a vacuous binder of another
  -- conjunction clause; it is never observed and adds no FFI policy.
  exact (Flapjack.Compiler.Backend.LabProps.shareMemOpAddClockSame
    { t with pc := count + t.pc } operator register address extra ffi bytes s2
    { name := .sharedMem .mappedRead, configuration := [], bytes := [], outcome := .failed } t).2.1
      ⟨hclock, hbase⟩

end Flapjack.Compiler.Backend.LabFilter.Proofs
