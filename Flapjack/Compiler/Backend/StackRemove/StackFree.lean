import Flapjack.Compiler.Backend.StackRemove

/-! Literal stack_removeScript.sml:89–102 stack-free instruction builders.
Both use the faithful native StackLang/Asm carriers. The executed runtime
still uses its existing StackRemove macros; actual replacement is tracked
on dependency-linked 36ez.3, so these definitions do not complete that route.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- One native immediate Add at HOL's numeric word offset; pointer and count
remain arbitrary naturals, with no added register-range or word-fit premise. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "single_stack_free_def"
  (words_as_type_indexed_bitvec)]
def singleStackFree {width : Nat} [NeZero width] (pointer count : Nat) : HolProg width :=
  .inst (.arith (.binop .add pointer pointer (.imm (wordOffset count))))

/-- Complete HOL recursion, including Skip at zero, the exact 255-word chunk
boundary and the ordered Seq for every larger count. Width wrapping happens
only through the original word_offset, before native instruction emission. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "stack_free_def"
  (words_as_type_indexed_bitvec)]
def stackFree {width : Nat} [NeZero width] (pointer count : Nat) : HolProg width :=
  if count = 0 then .skip
  else if count ≤ maxStackAlloc then singleStackFree pointer count
  else .seq (singleStackFree pointer maxStackAlloc) (stackFree pointer (count - maxStackAlloc))
termination_by count
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Flapjack equation fixture for the native original definition. -/
theorem stackFree_zero {width : Nat} [NeZero width] (pointer : Nat) :
    stackFree (width := width) pointer 0 = .skip := by simp [stackFree]

/-- Flapjack equation fixture; no additional HOL declaration is claimed. -/
theorem stackFree_small {width : Nat} [NeZero width] (pointer count : Nat)
    (nonzero : count ≠ 0) (small : count ≤ maxStackAlloc) :
    stackFree (width := width) pointer count = singleStackFree pointer count := by
  simp [stackFree, nonzero, small]

/-- Flapjack equation fixture preserving the ordered native source recursion. -/
theorem stackFree_large {width : Nat} [NeZero width] (pointer count : Nat)
    (large : maxStackAlloc < count) :
    stackFree (width := width) pointer count =
      .seq (singleStackFree pointer maxStackAlloc) (stackFree pointer (count - maxStackAlloc)) := by
  have nonzero : count ≠ 0 := by simp only [maxStackAlloc] at large; omega
  rw [stackFree, if_neg nonzero, if_neg (Nat.not_le.mpr large)]

end Flapjack.Compiler.Backend.StackRemove
