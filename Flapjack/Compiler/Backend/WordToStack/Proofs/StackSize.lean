import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-!
# Word-to-Stack stack size relation

Counterpart of word_to_stackProofScript.sml's stack_size_rel group. HOL
`the default option` is `Option.getD default`; subtraction remains saturating
Nat subtraction. Source and target stacks keep their exact list carriers.
-/
namespace Flapjack.WordToStackProofs

@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_size_rel_def"
  (words_as_type_indexed_bitvec)]
def stackSizeRel {width : Nat} [NeZero width]
    (frame : Nat) (localsSize : Option Nat) (stackLimit : Nat) (stackMax : Option Nat)
    (sourceStack : List (WordSemStackFrame width))
    (targetStack : List (WordLocW width)) (stackSpace extra : Nat) : Prop :=
  (frame ≠ 0 → localsSize.getD frame = frame) ∧
    stackLimit = targetStack.length ∧
    ∀ maximum, stackMax = some maximum →
      targetStack.length - stackSpace - frame - extra ≤ maximum ∧
      localsSize.isSome ∧
      ∃ size, wordSemStackSize sourceStack = some size ∧
        size = targetStack.length - stackSpace - frame - extra

/-- HOL's unconditional option-elimination equivalence. No stack relation,
conservative bound, successful evaluation, or initialized state is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_size_rel_iff"
  (words_as_type_indexed_bitvec)]
theorem stackSizeRel_iff {width : Nat} [NeZero width]
    (frame : Nat) (localsSize : Option Nat) (stackLimit : Nat) (stackMax : Option Nat)
    (sourceStack : List (WordSemStackFrame width))
    (targetStack : List (WordLocW width)) (stackSpace extra : Nat) :
    stackSizeRel frame localsSize stackLimit stackMax sourceStack targetStack stackSpace extra ↔
      (frame ≠ 0 → localsSize.getD frame = frame) ∧
      stackLimit = targetStack.length ∧
      targetStack.length - stackSpace - frame - extra ≤
        stackMax.getD (targetStack.length - stackSpace - frame - extra) ∧
      (stackMax.isSome → (wordSemStackSize sourceStack).isSome) ∧
      (stackMax.isSome → localsSize.isSome) ∧
      (stackMax.isSome → (wordSemStackSize sourceStack).getD
        (targetStack.length - stackSpace - frame - extra) =
          targetStack.length - stackSpace - frame - extra) := by
  cases localsSize <;> cases stackMax <;>
    cases hs : wordSemStackSize sourceStack <;>
    simp [stackSizeRel, hs]

end Flapjack.WordToStackProofs
