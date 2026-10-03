import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux

namespace Flapjack.WordToStackProofs

/-- Inhabitation for total HOL EL; does not select its unspecified value. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Full original stack relation. Source frames, target rest and bitmaps share
one word dimension; the separately observed target handler has an independent
word dimension, as recorded by the original polymorphic type. All conjuncts
and the original handler guard remain, with total HOL EL rather than a chosen
out-of-range frame. LASTN is drop(length-n), also for oversized n. No extra
range, successful-abstraction or representation premise is introduced. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_def"
  (words_as_type_indexed_bitvec)]
noncomputable def stackRel {width : Nat} {handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k sourceHandler : Nat) (sourceStack : List (WordSemStackFrame width))
    (targetHandler : Option (WordLocW handlerWidth))
    (targetRestOfStack : List (WordLocW width)) (targetStackLength : Nat)
    (targetBitmaps : List (BitVec width)) (lens : List Nat) : Prop :=
  sourceStack.all sortedEnv = true ∧
  ∃ stack,
    absStack targetBitmaps sourceStack targetRestOfStack lens = some stack ∧
    (sourceHandler < sourceStack.length →
      isHandlerFrame (Flapjack.holEl (sourceStack.length - (sourceHandler + 1)) sourceStack) = true →
      targetHandler = some (.word (BitVec.ofNat handlerWidth
        (targetStackLength - handlerVal (stack.drop (stack.length - (sourceHandler + 1))))))) ∧
    stackRelAux k targetStackLength sourceStack stack

end Flapjack.WordToStackProofs
