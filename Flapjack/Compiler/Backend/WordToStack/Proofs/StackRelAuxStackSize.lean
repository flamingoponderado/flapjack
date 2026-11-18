module

public import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux
public import Flapjack.Misc.MiscThe
public import Flapjack.Pancake.Proofs.LoopToWord.LastNAddCons

@[expose] public section

namespace Flapjack.WordToStackProofs

/-- Full original auxiliary stack-size result. Source-frame words, handler
locations and saved-handler words retain their independent dimensions. The
sole premise is the full auxiliary relation; absent size annotations and
mismatched/empty lists are included, with no success or frame-bound premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_stack_size"
  (words_as_type_indexed_bitvec)]
theorem stackRelAuxStackSize {locWidth width frameWidth : Nat}
    [NeZero locWidth] [NeZero width] [NeZero frameWidth]
    (len k : Nat) (source : List (WordSemStackFrame frameWidth))
    (stack : List (Option (WordLocW locWidth × WordLocW width) × List Bool ×
      List (WordLocW frameWidth)))
    (related : stackRelAux len k source stack) :
    miscThe (handlerVal stack) (wordSemStackSize source) = handlerVal stack := by
  induction source generalizing stack with
  | nil => cases stack with | nil => rfl | cons _ _ => simp [stackRelAux] at related
  | cons head sourceRest ih =>
    cases head with
    | stackFrame size nonGc gc sourceHandler =>
      cases stack with
      | nil => simp [stackRelAux] at related
      | cons entry rest =>
        rcases entry with ⟨targetHandler, bits, values⟩
        cases sourceHandler <;> cases targetHandler
        all_goals try solve | simp [stackRelAux] at related
        · rw [stackRelAux] at related
          obtain ⟨_, _, sizeEq, tailRel⟩ := related
          have tailSize := ih rest tailRel
          cases size with
          | none => simp [wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, miscThe]
          | some n =>
            simp only [Option.getD_some] at sizeEq
            subst n
            cases h : wordSemStackSize sourceRest
            all_goals
              simp only [wordSemStackSize, wordSemStackSizeFrame] at h tailSize ⊢
              simp_all [wordSemOptionAdd, miscThe, handlerVal]
              try omega
        · rw [stackRelAux] at related
          obtain ⟨_, _, _, _, sizeEq, tailRel⟩ := related
          have tailSize := ih rest tailRel
          cases size with
          | none => simp [wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, miscThe]
          | some n =>
            simp only [Option.getD_some] at sizeEq
            subst n
            cases h : wordSemStackSize sourceRest
            all_goals
              simp only [wordSemStackSize, wordSemStackSizeFrame] at h tailSize ⊢
              simp_all [wordSemOptionAdd, miscThe, handlerVal]
              try omega

/-- Exact HOL `stack_rel_aux_LENGTH` (`word_to_stackProofScript.sml:2438-2444`):
the auxiliary relation preserves the stack length. Source-frame words, handler
locations and saved-handler words retain their independent dimensions, and the
sole premise is the full relation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem stackRelAuxLength {locWidth width frameWidth : Nat}
    [NeZero locWidth] [NeZero width] [NeZero frameWidth]
    (len k : Nat) (source : List (WordSemStackFrame frameWidth))
    (stack : List (Option (WordLocW locWidth × WordLocW width) × List Bool ×
      List (WordLocW frameWidth)))
    (related : stackRelAux len k source stack) :
    source.length = stack.length := by
  induction source generalizing stack with
  | nil =>
    cases stack with
    | nil => rfl
    | cons _ _ => simp [stackRelAux] at related
  | cons head rest ih =>
    cases head with
    | stackFrame size nonGc gc handler =>
      cases stack with
      | nil => simp [stackRelAux] at related
      | cons entry stackRest =>
        rcases entry with ⟨targetHandler, bits, frame⟩
        cases handler with
        | none =>
          cases targetHandler with
          | none =>
            simp only [List.length_cons, stackRelAux] at related ⊢
            obtain ⟨_, _, _, tailRel⟩ := related
            have := ih stackRest tailRel
            omega
          | some _ => simp [stackRelAux] at related
        | some handler =>
          cases targetHandler with
          | none => simp [stackRelAux] at related
          | some targetHandler =>
            simp only [List.length_cons, stackRelAux] at related ⊢
            obtain ⟨_, _, _, _, _, tailRel⟩ := related
            have := ih stackRest tailRel
            omega

/-- Flapjack helper for `stack_rel_aux_LASTN`: taking the last `n` elements of
a list no longer than `n` returns the whole list (HOL `rich_list$LASTN_MORE`).
No separate HOL original. -/
theorem wordSemLastN_of_length_le {α : Type} {l : List α} {n : Nat}
    (h : l.length ≤ n) : wordSemLastN n l = l := by
  unfold wordSemLastN
  have hr : l.reverse.length ≤ n := by
    rw [List.length_reverse]
    exact h
  rw [List.take_of_length_le hr, List.reverse_reverse]

/-- Exact HOL `stack_rel_aux_LASTN` (`word_to_stackProofScript.sml:2447-2457`):
the auxiliary relation is preserved by taking the last `n` elements of both
stacks. Binders follow the typed capture (`k`, `len`, `xs`, `ys`, `n`); the
last-`n` operation is the reviewed `wordSemLastN` rendering of `LASTN`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_LASTN"
  (words_as_type_indexed_bitvec)]
theorem stackRelAuxLastN {locWidth width frameWidth : Nat}
    [NeZero locWidth] [NeZero width] [NeZero frameWidth]
    (len k : Nat) (source : List (WordSemStackFrame frameWidth))
    (stack : List (Option (WordLocW locWidth × WordLocW width) × List Bool ×
      List (WordLocW frameWidth))) (n : Nat)
    (related : stackRelAux len k source stack) :
    stackRelAux len k (wordSemLastN n source) (wordSemLastN n stack) := by
  induction source generalizing stack n with
  | nil =>
    cases stack with
    | nil => simp [wordSemLastN, stackRelAux]
    | cons _ _ => simp [stackRelAux] at related
  | cons head rest ih =>
    cases head with
    | stackFrame size nonGc gc handler =>
      cases stack with
      | nil => simp [stackRelAux] at related
      | cons entry stackRest =>
        rcases entry with ⟨targetHandler, bits, frame⟩
        cases handler with
        | none =>
          cases targetHandler with
          | none =>
            simp only [stackRelAux] at related
            have tailRel : stackRelAux len k rest stackRest := related.2.2.2
            have lengthEq := stackRelAuxLength len k rest stackRest tailRel
            cases n with
            | zero => simp [wordSemLastN, stackRelAux]
            | succ m =>
              by_cases hlen : m < rest.length
              · rw [Flapjack.LoopToWord.wordSemLastN_add_cons _ _ _ (by omega),
                  Flapjack.LoopToWord.wordSemLastN_add_cons _ _ _ (by omega)]
                exact ih stackRest (m + 1) tailRel
              · have hsrc : rest.length + 1 ≤ m + 1 := by omega
                have htgt : stackRest.length + 1 ≤ m + 1 := by omega
                rw [wordSemLastN_of_length_le hsrc, wordSemLastN_of_length_le htgt]
                rw [stackRelAux]
                exact related
          | some _ => simp [stackRelAux] at related
        | some handler =>
          cases targetHandler with
          | none => simp [stackRelAux] at related
          | some targetHandler =>
            simp only [stackRelAux] at related
            have tailRel : stackRelAux len k rest stackRest := related.2.2.2.2.2
            have lengthEq := stackRelAuxLength len k rest stackRest tailRel
            cases n with
            | zero => simp [wordSemLastN, stackRelAux]
            | succ m =>
              by_cases hlen : m < rest.length
              · rw [Flapjack.LoopToWord.wordSemLastN_add_cons _ _ _ (by omega),
                  Flapjack.LoopToWord.wordSemLastN_add_cons _ _ _ (by omega)]
                exact ih stackRest (m + 1) tailRel
              · have hsrc : rest.length + 1 ≤ m + 1 := by omega
                have htgt : stackRest.length + 1 ≤ m + 1 := by omega
                rw [wordSemLastN_of_length_le hsrc, wordSemLastN_of_length_le htgt]
                rw [stackRelAux]
                exact related

end Flapjack.WordToStackProofs
