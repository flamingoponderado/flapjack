import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Integer Inst case with the original fallback clauses. Source map bounds and
allocation class establish the fresh destination constraints. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.
theorem ssaCcTrans_fullInstInst {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (instruction : WordLangInst (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.inst instruction) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config (.inst instruction) = true) :
    fullInstOkLessExact config (ssaCcTrans (.inst instruction) ssa next tables).1 = true := by
  have allocated := h.2.1
  have positive : 0 < next := by
    simp only [isAllocVar, decide_eq_true_eq] at allocated
    omega
  have lookupBound : ∀ key, optionLookup ssa key < next := by
    intro key
    unfold optionLookup
    cases found : sptLookup key ssa with
    | none => simpa using positive
    | some value => exact (h.2.2.1 key value found).2
  have lookupNe : ∀ key, next ≠ optionLookup ssa key :=
    fun key => Nat.ne_of_gt (lookupBound key)
  have lookupNeReverse : ∀ key, optionLookup ssa key ≠ next :=
    fun key => (lookupNe key).symm
  have sourceValid := h.2.2.2
  revert sourceValid h
  simp only [ssaCcTrans]
  fun_cases ssaCcTransInst instruction ssa next <;> intro h sourceValid <;>
    simp_all [nextVarRename, fullInstOkLessExact, fullInstOkLessWith,
      HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
      HolAddr.ofWordLangAddr, instOkLessExact] <;> try omega
  case case4 =>
    rename_i operator destination source immediate fresh tree counter mapped notReg producer
    cases immediate <;> simp_all
  case case6 =>
    rename_i operator destination source immediate fresh tree counter mapped notReg producer
    cases immediate <;> simp_all
  case case8 =>
    right
    constructor
    · exact lookupNe _
    · omega
  case case9 => exact Or.inr (lookupNe _)
  case case10 => exact Or.inr (lookupNe _)

end Flapjack.WordAlloc
