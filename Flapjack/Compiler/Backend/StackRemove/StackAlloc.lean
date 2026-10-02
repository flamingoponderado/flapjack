import Flapjack.Compiler.Backend.StackRemove

/-! Literal native allocation builders from stack_removeScript.sml:65–86.
The default Pancake and assembly modes initializedRuntimeLab? executes these native
definitions through StackRemove.compileHOL. hex and sections modes retain the legacy
route; upstream StackAlloc replacement is a separate obligation.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Preserve both original overflow-check forms after the immediate Sub. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "single_stack_alloc_def"
  (words_as_type_indexed_bitvec)]
def singleStackAlloc {width : Nat} [NeZero width] (jump : Bool) (pointer count : Nat) :
    HolProg width :=
  if jump then
    .seq (.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset count)))))
      (.jumpLower pointer (pointer + 1) stackErrLab)
  else
    .seq (.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset count)))))
      (.ite .lower pointer (.reg (pointer + 1)) (haltInst 2) .skip)

/-- Full original zero/small/chunked allocation recursion, retaining every check. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "stack_alloc_def"
  (words_as_type_indexed_bitvec)]
def stackAlloc {width : Nat} [NeZero width] (jump : Bool) (pointer count : Nat) :
    HolProg width :=
  if count = 0 then .skip
  else if count ≤ maxStackAlloc then singleStackAlloc jump pointer count
  else .seq (singleStackAlloc jump pointer maxStackAlloc)
    (stackAlloc jump pointer (count - maxStackAlloc))
termination_by count
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Flapjack source-equation fixture, not a separately named HOL theorem. -/
theorem stackAlloc_large {width : Nat} [NeZero width] (jump : Bool) (pointer count : Nat)
    (large : maxStackAlloc < count) :
    stackAlloc (width := width) jump pointer count =
      .seq (singleStackAlloc jump pointer maxStackAlloc)
        (stackAlloc jump pointer (count - maxStackAlloc)) := by
  have nonzero : count ≠ 0 := by simp only [maxStackAlloc] at large; omega
  rw [stackAlloc, if_neg nonzero, if_neg (Nat.not_le.mpr large)]

end Flapjack.Compiler.Backend.StackRemove
