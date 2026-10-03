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

end Flapjack.Compiler.Backend.LabFilter.Proofs
