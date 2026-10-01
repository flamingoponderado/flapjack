import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-! Literal frame predicates used by the Word-to-Stack stack relation. -/
namespace Flapjack.WordToStackProofs

/-- Number of target words occupied by the abstract frames, including the
terminal word and the handler header when present. The handler payload,
ignored middle field and frame elements have independent arbitrary types,
as in HOL; this calculation observes only SOME/NONE and list lengths. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "handler_val_def"]
def handlerVal {α β γ : Type} : List (Option α × β × List γ) → Nat
  | [] => 1
  | (none, _, frame) :: stack => 1 + frame.length + handlerVal stack
  | (some _, _, frame) :: stack => 4 + frame.length + handlerVal stack

/-- The faithful source frame has a handler exactly when its final field is SOME. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "is_handler_frame_def"
  (words_as_type_indexed_bitvec)]
def isHandlerFrame {width : Nat} [NeZero width] : WordSemStackFrame width → Bool
  | .stackFrame _ _ _ none => false
  | _ => true

/-- Descending keys in the GC cutset. HOL sorting$SORTED_DEF checks adjacent
pairs (not all pairs); zip with tail enumerates precisely those comparisons. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "sorted_env_def"
  (words_as_type_indexed_bitvec)]
def sortedEnv {width : Nat} [NeZero width] : WordSemStackFrame width → Bool
  | .stackFrame _ _ gcCutset _ =>
      (gcCutset.zip gcCutset.tail).all (fun (left, right) => decide (left.1 > right.1))

end Flapjack.WordToStackProofs
