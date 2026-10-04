import Flapjack.Compiler.Backend.StackRemove.Proofs.LabelBuilders
import Flapjack.Compiler.Backend.StackRemove.Proofs.CodeRelation
namespace Flapjack.Compiler.Backend.StackRemove.LabelPreservation
open Flapjack.Compiler.Backend.StackRemove
open Flapjack Flapjack.StackSem Flapjack.Compiler.Backend.StackLang LabelBuilders
/-- Compilation preserves the complete continuation-label predicate on every native constructor. No register-bound premise is needed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem labelsComp {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) (program : HolProg width) :
    getLabelsExact (comp jump bounds pointer program) = getLabelsExact program := by
  induction program using comp.induct bounds <;>
    try simp_all [comp, getLabelsExact, labelsStackFree, labelsStackAlloc,
      stackStore, stackLoad,
      copyLoop, copyEach, listSeqHOL, whileProg, whileHOL, moveInst, moveHOL,
      addInst, subInst, leftShiftInst, rightShiftInst, loadInst, storeInst,
      addBytesInWordInst]
  all_goals try
    split <;> simp [getLabelsExact, labelsUpshift, labelsDownshift]
  case case22 ret target handler ihHandler ihReturn =>
    cases ret with
    | none =>
      cases handler with
      | none => simp [comp, getLabelsExact]
      | some handler =>
        obtain ⟨body, first, second⟩ := handler
        simp [comp, getLabelsExact]
    | some ret =>
      obtain ⟨body, register, first, second⟩ := ret
      cases handler with
      | none => simp_all [comp, getLabelsExact]
      | some handler =>
        obtain ⟨handlerBody, handlerFirst, handlerSecond⟩ := handler
        simp_all [comp, getLabelsExact]
/-- The full native code relation transports a successful source location check. Target lookup and label membership are derived, not assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem codeRelLocCheck {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : Spt (HolProg width)) (first second : Nat)
    (h : codeRelHOL jump bounds pointer source target ∧ locCheckExact source (first, second)) :
    locCheckExact target (first, second) := by
  obtain ⟨relation, checked⟩ := h
  rcases checked with ⟨zero, member⟩ | ⟨key, program, lookup, label⟩
  · refine Or.inl ⟨zero, ?_⟩
    change sptDomain target first
    rw [relation.2]
    exact Or.inl member
  · exact Or.inr ⟨key, comp jump bounds pointer program, (relation.1 key program lookup).2,
      by rw [labelsComp]; exact label⟩
end Flapjack.Compiler.Backend.StackRemove.LabelPreservation
