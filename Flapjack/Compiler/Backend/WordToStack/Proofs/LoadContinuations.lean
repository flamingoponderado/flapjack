import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels

namespace Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSem

/-- Full original ordered-load append law, as equality of whole native
continuation functions. Arbitrary register/frame indices, repetitions, empty
lists and every continuation constructor are retained; no bounds are assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wStackLoad_append"
  (words_as_type_indexed_bitvec)]
theorem wStackLoadAppend {width : Nat} [NeZero width] (l1 l2 : List (Nat × Nat)) :
    (wStackLoadNative (l1 ++ l2) : HolProg width → HolProg width) =
      wStackLoadNative l1 ∘ wStackLoadNative l2 := by
  funext p
  induction l1 with
  | nil => rfl
  | cons load l1 ih =>
      rcases load with ⟨reg,slot⟩
      simpa only [List.cons_append, wStackLoadNative, Function.comp_apply] using
        congrArg (Flapjack.Compiler.Backend.StackLang.Prog.seq (.stackLoad reg slot)) ih

/-- Full original label-set equality for the actual native ordered loads and
arbitrary continuation. Both sides are entire predicates on label pairs, not
merely membership at selected labels or a source/target label assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_labels_wStackLoad"
  (words_as_type_indexed_bitvec)]
theorem getLabelsWStackLoad {width : Nat} [NeZero width]
    (xs : List (Nat × Nat)) (p : HolProg width) :
    getLabelsExact (wStackLoadNative xs p) = getLabelsExact p := by
  induction xs with
  | nil => rfl
  | cons load xs ih =>
      rcases load with ⟨reg,slot⟩
      funext label
      simpa only [wStackLoadNative, getLabelsExact, false_or] using congrFun ih label

end Flapjack.WordToStackProofs
