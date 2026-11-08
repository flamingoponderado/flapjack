import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux
import Flapjack.Misc.MiscThe

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

end Flapjack.WordToStackProofs
