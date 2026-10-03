import Flapjack.Compiler.Backend.WordAlloc.SSATransInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterClass

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full HOL SSA instruction counter/allocation/map invariant. The actual native
instruction compiler output equality precedes the original map/allocation
premises. All instruction constructors, including both FP word-width branches,
retain the monotonic counter, allocated counter and output-map bounds. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_inst_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransInstProps {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTransInst instruction ssa next = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  have allocation4 := isAllocVarAdd next h.2
  have allocation8 := isAllocVarAdd (next + 4) allocation4
  have nonphysical : ¬ isPhyVar next := by
    simp only [isAllocVar, decide_eq_true_eq] at h
    simp only [isPhyVar, decide_eq_true_eq]; omega
  have nonphysical4 : ¬ isPhyVar (next + 4) := by
    simp only [isAllocVar, decide_eq_true_eq] at allocation4
    simp only [isPhyVar, decide_eq_true_eq]; omega
  have map4 (name : Nat) := ssaMapOKExtend next ssa name ⟨h.1, nonphysical⟩
  have map8 (first second : Nat) :=
    ssaMapOKExtend (next + 4) (sptInsert first next ssa) second ⟨map4 first, nonphysical4⟩
  cases instruction
  case arith operation =>
    cases operation
    case binop operator left right immediate =>
      cases immediate
      all_goals
        simp only [ssaCcTransInst, nextVarRename] at produced
        repeat first | split at produced
        simp only [Prod.mk.injEq] at produced
        obtain ⟨_, rfl, rfl⟩ := produced
        first
          | exact ⟨Nat.le_refl _, h.2, h.1⟩
          | exact ⟨by omega, allocation4, map4 _⟩
          | exact ⟨by omega, allocation8, map8 _ _⟩
    case shift operator left right immediate =>
      cases immediate
      all_goals
        simp only [ssaCcTransInst, nextVarRename] at produced
        repeat first | split at produced
        simp only [Prod.mk.injEq] at produced
        obtain ⟨_, rfl, rfl⟩ := produced
        first
          | exact ⟨Nat.le_refl _, h.2, h.1⟩
          | exact ⟨by omega, allocation4, map4 _⟩
          | exact ⟨by omega, allocation8, map8 _ _⟩
    all_goals
      simp only [ssaCcTransInst, nextVarRename] at produced
      repeat first | split at produced
      simp only [Prod.mk.injEq] at produced
      obtain ⟨_, rfl, rfl⟩ := produced
      first
        | exact ⟨Nat.le_refl _, h.2, h.1⟩
        | exact ⟨by omega, allocation4, map4 _⟩
        | exact ⟨by omega, allocation8, map8 _ _⟩
  case mem operation register address =>
    cases operation <;> cases address
    all_goals
      simp only [ssaCcTransInst, nextVarRename] at produced
      repeat first | split at produced
      simp only [Prod.mk.injEq] at produced
      obtain ⟨_, rfl, rfl⟩ := produced
      first
        | exact ⟨Nat.le_refl _, h.2, h.1⟩
        | exact ⟨by omega, allocation4, map4 _⟩
        | exact ⟨by omega, allocation8, map8 _ _⟩
  case fp operation =>
    cases operation
    all_goals simp only [ssaCcTransInst, nextVarRename] at produced
    all_goals repeat first | split at produced
    all_goals repeat first | split at produced
    all_goals simp only [Prod.mk.injEq] at produced
    all_goals obtain ⟨_, rfl, rfl⟩ := produced
    all_goals first
      | exact ⟨Nat.le_refl _, h.2, h.1⟩
      | exact ⟨by omega, allocation4, map4 _⟩
      | exact ⟨by omega, allocation8, map8 _ _⟩
  all_goals
    simp only [ssaCcTransInst, nextVarRename] at produced
    repeat first | split at produced
    simp only [Prod.mk.injEq] at produced
    obtain ⟨_, rfl, rfl⟩ := produced
    first
      | exact ⟨Nat.le_refl _, h.2, h.1⟩
      | exact ⟨by omega, allocation4, map4 _⟩
      | exact ⟨by omega, allocation8, map8 _ _⟩

end Flapjack.Compiler.Backend.WordAlloc
