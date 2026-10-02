import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels

namespace Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSem

/-- Full original return-copy recursion conjunction, including the exact
right-nested `list_Seq` tree. No register, frame, count or width bound is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_thm"
  (words_as_type_indexed_bitvec)]
theorem copyRetAuxThm {width : Nat} [NeZero width] (k f n : Nat) :
    (copyRetAuxNative k f 0 : HolProg width) = .skip ∧
    (copyRetAuxNative k f (n + 1) : HolProg width) =
      listSeq [.stackLoad k n, .stackStore k (n + f), copyRetAuxNative k f n] := by
  exact ⟨rfl, rfl⟩

/-- Flapjack-specific induction support: the whole label predicate of the
actual native recursive return-copy body is empty. HOL proves this intermediate
fact inside `get_labels_copy_ret`, rather than declaring it separately. -/
private theorem copyRetAuxLabels {width : Nat} [NeZero width] (k f n : Nat) :
    getLabelsExact (copyRetAuxNative (width := width) k f n) = fun _ => False := by
  induction n with
  | zero => simp [copyRetAuxNative, getLabelsExact]
  | succ n ih =>
      funext label
      simpa only [copyRetAuxNative, listSeq, getLabelsExact, false_or] using
        congrFun ih label

/-- Full original whole label-set preservation of the actual native return
copy/free wrapper, for every continuation and both Boolean modes. The original
return-value and unused third frame-component carriers remain independent of
each other and of the word-indexed continuation; no extra premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_labels_copy_ret"
  (words_as_type_indexed_bitvec)]
theorem getLabelsCopyRet {width : Nat} [NeZero width] {β γ : Type}
    (perf isHandle : Bool) (kf : Nat × Nat × γ) (vs : List β) (q : HolProg width) :
    getLabelsExact (copyRetNative perf isHandle kf vs q) = getLabelsExact q := by
  by_cases zero : Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 vs = 0
  · simp [copyRetNative, zero]
  · funext label
    simp [copyRetNative, zero, getLabelsExact, copyRetAuxLabels, seqStackFreeNative]

end Flapjack.WordToStackProofs
