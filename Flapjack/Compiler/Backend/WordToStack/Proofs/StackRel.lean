import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux

/-! Literal Word-to-Stack `stack_rel` over exact carriers. -/
namespace Flapjack.WordToStackProofs

/-- Literal source `stack_rel` (`word_to_stackProofScript.sml:846`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_def"
  (words_as_type_indexed_bitvec)]
def stackRel {width : Nat} [NeZero width] (k sHandler : Nat)
    (sStack : List (WordSemStackFrame width))
    (tHandler : Option (WordLocW width)) (tRestOfStack : List (WordLocW width))
    (tStackLength : Nat) (tBitmaps : List (BitVec width)) (lens : List Nat) : Prop :=
  sStack.all sortedEnv = true ∧
  ∃ stack,
    absStack tBitmaps sStack tRestOfStack lens = some stack ∧
    (sHandler < sStack.length →
        isHandlerFrame (holEl (sStack.length - (sHandler + 1)) sStack holElDefaultFrame) →
        tHandler =
          some (.word (BitVec.ofNat width
            (tStackLength - handlerVal (lastN (sHandler + 1) stack))))) ∧
    stackRelAux k tStackLength sStack stack

end Flapjack.WordToStackProofs
