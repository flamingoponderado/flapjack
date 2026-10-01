import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux

/-! Literal Word-to-Stack `stack_rel` over exact carriers. -/
namespace Flapjack.WordToStackProofs

/-- Literal source `stack_rel` (`word_to_stackProofScript.sml:846`), kept
PROVISIONAL and untagged: like `stackRelAux` it uses the untagged `holEl`/
`holElDefaultFrame`/`holThe`/`lastN` renderings of HOL's total `EL`/`the`.
Faithful total-list rendering + HOL `listScript` provenance are tracked by
`flapjack-pxn.18.5.15.3.38` and `.38.1`; not an accepted exact HOL port yet. -/
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
