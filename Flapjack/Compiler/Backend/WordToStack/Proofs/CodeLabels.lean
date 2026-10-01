import Flapjack.Compiler.Backend.StackProps.CodeLabels
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeReturn

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Complete source conjunction for arbitrary load lists and continuations. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "get_code_handler_labels_wStackLoad" (words_as_type_indexed_bitvec)]
theorem getCodeHandlerLabelsWStackLoad {width : Nat} [NeZero width]
    (ls : List (Nat × Nat)) (x : HolProg width) (owner : Nat) :
    getCodeLabels (wStackLoadNative ls x) = getCodeLabels x ∧
    stackGetHandlerLabels owner (wStackLoadNative ls x) = stackGetHandlerLabels owner x := by
  induction ls with
  | nil => simp [wStackLoadNative]
  | cons pair ls ih =>
    rcases pair with ⟨r, i⟩
    simpa [wStackLoadNative, getCodeLabels, stackGetHandlerLabels] using ih

/-- Original output equation, including the returned bitmap component. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wLive_code_labels" (words_as_type_indexed_bitvec)]
theorem wLiveCodeLabels {width : Nat} [NeZero width]
    (q : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) (out : HolProg width) (bsOut : AppList (BitVec width) × Nat)
    (h : wLiveNative q bs kf = (out, bsOut)) : getCodeLabels out = ∅ := by
  have eq := congrArg Prod.fst h
  change (wLiveNative q bs kf).1 = out at eq
  rw [← eq]
  by_cases empty : kf.2.1 = 0 <;> simp [wLiveNative, empty, getCodeLabels]

/-- Complete code-label preservation for arbitrary slot movement parameters. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_code_labels" (words_as_type_indexed_bitvec)]
theorem stackMoveCodeLabels {width : Nat} [NeZero width]
    (a b c d : Nat) (e : HolProg width) :
    getCodeLabels (stackMoveNative a b c d e) = getCodeLabels e := by
  induction a generalizing b with
  | zero => simp [stackMoveNative]
  | succ a ih => simp [stackMoveNative, getCodeLabels, ih]

/-- Both complete source label sets of the return-copy loop are empty. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "get_code_handler_labels_copy_ret_aux" (words_as_type_indexed_bitvec)]
theorem getCodeHandlerLabelsCopyRetAux {width : Nat} [NeZero width]
    (k f n owner : Nat) :
    getCodeLabels (copyRetAuxNative k f n : HolProg width) = ∅ ∧
    stackGetHandlerLabels owner (copyRetAuxNative k f n : HolProg width) = ∅ := by
  induction n with
  | zero => simp [copyRetAuxNative, getCodeLabels, stackGetHandlerLabels]
  | succ n ih => simpa [copyRetAuxNative, listSeq, getCodeLabels, stackGetHandlerLabels] using ih

/-- Complete source conjunction for arbitrary return-list payloads and both flags. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "get_code_handler_labels_copy_ret" (words_as_type_indexed_bitvec)]
theorem getCodeHandlerLabelsCopyRet {width : Nat} [NeZero width] {β : Type}
    (perf b : Bool) (kf : Nat × Nat × Nat) (vs : List β)
    (kont : HolProg width) (owner : Nat) :
    getCodeLabels (copyRetNative perf b kf vs kont) = getCodeLabels kont ∧
    stackGetHandlerLabels owner (copyRetNative perf b kf vs kont) =
      stackGetHandlerLabels owner kont := by
  simp only [copyRetNative]
  split
  · exact ⟨rfl, rfl⟩
  · have labels := getCodeHandlerLabelsCopyRetAux (width := width) kf.1
      (if b then kf.2.1 + WordToStack.handlerSlots perf else kf.2.1)
      (WordToStack.numStackRet kf.1 vs) owner
    simp only [getCodeLabels, stackGetHandlerLabels, labels.1, labels.2, Set.empty_union]
    by_cases zero : WordToStack.numStackRet kf.1 vs = 0 <;>
      simp [seqStackFreeNative, zero, getCodeLabels, stackGetHandlerLabels]

end Flapjack.Compiler.Backend.WordToStack.Native
