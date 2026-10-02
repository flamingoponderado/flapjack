import Mathlib.Data.List.Defs
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLength
import Flapjack.Compiler.Backend.Semantics.WordSem.Env

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Literal abstract-frame equality: only the final list lengths are observed,
so their element types remain independent, as in the original declaration. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_frame_eq_def"]
def absFrameEq {α β γ δ : Type} (p : α × β × List γ) (q : α × β × List δ) : Prop :=
  p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.length = q.2.2.length

/-- Flapjack computation instance for the literal relation; it has no separate
HOL declaration and assumes equality only for fields compared by HOL. -/
instance {α β γ δ : Type} [DecidableEq α] [DecidableEq β]
    (p : α × β × List γ) (q : α × β × List δ) : Decidable (absFrameEq p q) := by
  unfold absFrameEq
  infer_instance

/-- Full original pointwise abstract-frame equality preserves handler offsets.
The handler and bitmap carriers are shared, while frame element types are
independent. No abstraction success or frame-shape premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "LIST_REL_abs_frame_eq_handler_val"]
theorem listRelAbsFrameEqHandlerVal {α β γ δ : Type}
    (xs : List (Option α × β × List γ)) (ys : List (Option α × β × List δ))
    (h : List.Forall₂ absFrameEq xs ys) : handlerVal xs = handlerVal ys := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy htail ih =>
    rcases x with ⟨handler, bits, frame⟩
    rcases y with ⟨handler', bits', frame'⟩
    change handler = handler' ∧ bits = bits' ∧ frame.length = frame'.length at hxy
    obtain ⟨hh, _, hl⟩ := hxy
    subst handler'
    cases handler <;> simp only [handlerVal, hl, ih]

/-- Full original successful-abstraction length theorem from the decoder
section. Its conclusion is identical to abs_stack_LENGTH; the existing full
native proof establishes it without an added relation or range premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "abs_stack_to_stack_LENGTH" (words_as_type_indexed_bitvec)]
theorem absStackToStackLength {width : Nat} {frameWidth : Nat}
    [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (wstack : List (WordSemStackFrame frameWidth))
    (sstack : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack bs wstack sstack lens = some stack) :
    handlerVal stack = sstack.length := absStackLength bs wstack sstack lens stack h

/-- Flapjack proof infrastructure: dropping abstract frames cannot increase
occupied words. No separate HOL declaration is claimed for this helper. -/
private theorem handlerValDropLe {α β γ : Type}
    (xs : List (Option α × β × List γ)) (n : Nat) :
    handlerVal (xs.drop n) ≤ handlerVal xs := by
  induction xs generalizing n with
  | nil => simp [handlerVal]
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      rcases x with ⟨handler, bits, frame⟩
      have h := ih n
      cases handler <;> simp only [List.drop_succ_cons, handlerVal] <;> omega

/-- Full original total LASTN identity at and beyond the list length. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_MORE"]
theorem lastNMore {α : Type} (ls : List α) (n : Nat) (h : ¬ n < ls.length) :
    wordSemLastN n ls = ls := by
  have hn : ls.reverse.length ≤ n := by simp only [List.length_reverse]; omega
  simp only [wordSemLastN, List.take_of_length_le hn, List.reverse_reverse]

/-- Full original suffix bound, for every handler index including zero and
indices beyond the abstract stack. Native LASTN keeps its original total list
behavior; only successful abstraction is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_len"
  (words_as_type_indexed_bitvec)]
theorem absStackLen {width : Nat} {frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (wstack : List (WordSemStackFrame frameWidth))
    (sstack : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (handler : Nat) (h : absStack bs wstack sstack lens = some stack) :
    handlerVal (wordSemLastN handler stack) ≤ sstack.length := by
  rw [← absStackLength bs wstack sstack lens stack h]
  simpa only [wordSemLastN, List.take_reverse, List.reverse_reverse] using
    handlerValDropLe stack (stack.length - handler)

end Flapjack.WordToStackProofs
