import Flapjack.Compiler.Backend.StackRemove.StackFree
import Flapjack.Compiler.Backend.StackRemove.StackAlloc
import Flapjack.Compiler.Backend.StackRemove.StackAddress
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels
/-! Exact local label-emptiness prerequisites of StackRemove correctness.
HOL sets use predicate equality. Every count, register and positive word width
is unrestricted; chunk recursion and both allocation branches are retained. -/
namespace Flapjack.Compiler.Backend.StackRemove.LabelBuilders
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.StackSem
/-- Freeing any number of stack words introduces no continuation labels. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_stack_free"
  (words_as_type_indexed_bitvec)]
theorem labelsStackFree {width : Nat} [NeZero width] (pointer count : Nat) :
    getLabelsExact (stackFree (width := width) pointer count) = (fun _ => False) := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    rw [stackFree]
    split
    · simp [getLabelsExact]
    · split
      · simp [getLabelsExact, singleStackFree]
      · simp only [getLabelsExact, singleStackFree]
        rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega)]
        simp
/-- Both allocation overflow-check forms introduce no continuation labels. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_stack_alloc"
  (words_as_type_indexed_bitvec)]
theorem labelsStackAlloc {width : Nat} [NeZero width] (jump : Bool) (pointer count : Nat) :
    getLabelsExact (stackAlloc (width := width) jump pointer count) = (fun _ => False) := by
  have single (n : Nat) : getLabelsExact (singleStackAlloc (width := width) jump pointer n) = (fun _ => False) := by
    cases jump <;> simp [singleStackAlloc, getLabelsExact, haltInst]
  induction count using Nat.strongRecOn with
  | ind count ih =>
    rw [stackAlloc]
    split
    · simp [getLabelsExact]
    · split
      · exact single count
      · simp only [getLabelsExact]
        rw [single, ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega)]
        simp
/-- The full chunked upward address shift introduces no continuation labels. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_upshift"
  (words_as_type_indexed_bitvec)]
theorem labelsUpshift {width : Nat} [NeZero width] (register count : Nat) :
    getLabelsExact (upshift (width := width) register count) = (fun _ => False) := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    rw [upshift]
    split
    · simp [getLabelsExact]
    · simp only [getLabelsExact]
      rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega)]
      simp
/-- The full chunked downward address shift introduces no continuation labels. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_downshift"
  (words_as_type_indexed_bitvec)]
theorem labelsDownshift {width : Nat} [NeZero width] (register count : Nat) :
    getLabelsExact (downshift (width := width) register count) = (fun _ => False) := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    rw [downshift]
    split
    · simp [getLabelsExact]
    · simp only [getLabelsExact]
      rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega)]
      simp
end Flapjack.Compiler.Backend.StackRemove.LabelBuilders
