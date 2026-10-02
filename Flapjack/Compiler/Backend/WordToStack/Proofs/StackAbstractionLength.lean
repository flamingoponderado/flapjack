import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction
import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames
import Lean.Elab.Tactic.Omega

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Full original empty-source abstraction result, with arbitrary bitmap/input
lists. Ignored source frame words retain their independent dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_empty"
  (words_as_type_indexed_bitvec)]
theorem absStackEmpty {width : Nat} {frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (ls : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack (frameWidth := frameWidth) bs [] ls lens = some stack) :
    ls = [.word 0] ∧ lens = [] := by
  cases lens with
  | nil =>
    rw [absStack] at h
    split at h
    · exact ⟨by assumption, rfl⟩
    · contradiction
  | cons n ns => simp [absStack] at h

/-- Full original nonempty-source abstraction of an empty target stack. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_CONS_NIL"
  (words_as_type_indexed_bitvec)]
theorem absStackConsNil {width : Nat} {frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bm : List (BitVec width)) (x : WordSemStackFrame frameWidth)
    (rest : List (WordSemStackFrame frameWidth)) (l : List Nat) :
    absStack bm (x :: rest) [] l = none := by
  cases x with
  | stackFrame size l0 locals handler =>
    cases l <;> cases handler <;> simp [absStack]

/-- Full original successful abstraction length invariant, covering every
normal and handler frame, including the terminal sentinel. Source bitmap and
saved-frame dimensions follow the reviewed absStack carrier; no validity,
frame-size, state-relation or target result premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem absStackLength {width : Nat} {frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bitmaps : List (BitVec width)) (wstack : List (WordSemStackFrame frameWidth))
    (tstack : List (WordLocW width)) (lens : List Nat)
    (astack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack bitmaps wstack tstack lens = some astack) :
    handlerVal astack = tstack.length := by
  induction wstack generalizing tstack lens astack with
  | nil =>
    obtain ⟨hs, hl⟩ := absStackEmpty bitmaps tstack lens astack h
    subst lens
    subst tstack
    simp [absStack] at h
    subst astack
    rfl
  | cons frame frames ih =>
    cases frame with
    | stackFrame size l0 locals handler =>
      cases lens with
      | nil => simp [absStack] at h
      | cons len lens =>
        cases tstack with
        | nil => simp [absStack] at h
        | cons header stack =>
          cases handler with
          | none =>
            rw [absStack] at h
            cases hr : StackSem.fullReadBitmap bitmaps header with
            | none => simp [hr] at h
            | some bits =>
              simp only [hr] at h
              split at h
              · contradiction
              · split at h
                · contradiction
                · cases he : absStack bitmaps frames (stack.drop len) lens with
                  | none => simp [he] at h
                  | some tail =>
                    simp only [he, Option.some.injEq] at h
                    rw [← h, handlerVal, ih (stack.drop len) lens tail he]
                    simp only [List.length_take, List.length_drop, List.length_cons]
                    omega
          | some payload =>
            cases stack with
            | nil => simp [absStack] at h
            | cons loc stack =>
              cases stack with
              | nil => simp [absStack] at h
              | cons hv stack =>
                cases stack with
                | nil => simp [absStack] at h
                | cons word stack =>
                  rw [absStack] at h
                  split at h
                  · contradiction
                  · cases hr : StackSem.fullReadBitmap bitmaps word with
                    | none => simp [hr] at h
                    | some bits =>
                      simp only [hr] at h
                      split at h
                      · contradiction
                      · split at h
                        · contradiction
                        · cases he : absStack bitmaps frames (stack.drop len) lens with
                          | none => simp [he] at h
                          | some tail =>
                            simp only [he, Option.some.injEq] at h
                            rw [← h, handlerVal, ih (stack.drop len) lens tail he]
                            simp only [List.length_take, List.length_drop, List.length_cons]
                            omega

/-- Full original impossibility of successful abstraction from an empty target. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_empty'"
  (words_as_type_indexed_bitvec)]
theorem absStackEmptyTarget {width : Nat} {frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (xs : List (WordSemStackFrame frameWidth)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width))) :
    absStack bs xs [] lens = some stack ↔ False := by
  cases xs with
  | nil => cases lens <;> simp [absStack]
  | cons x rest => simp [absStackConsNil]

end Flapjack.WordToStackProofs
