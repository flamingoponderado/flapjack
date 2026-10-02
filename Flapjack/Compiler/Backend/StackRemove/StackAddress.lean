import Flapjack.Compiler.Backend.StackRemove

/-! Native address builders from stack_removeScript.sml:104–137.
The default Pancake and assembly modes initializedRuntimeLab? executes these native
definitions through StackRemove.compileHOL. hex and sections modes retain the legacy
route; upstream StackAlloc replacement is a separate obligation.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Literal immediate Add recursion. Zero retains an instruction. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "upshift_def"
  (words_as_type_indexed_bitvec)]
def upshift {width : Nat} [NeZero width] (register count : Nat) : HolProg width :=
  if count ≤ maxStackAlloc then
    .inst (.arith (.binop .add register register (.imm (wordOffset count))))
  else
    .seq (.inst (.arith (.binop .add register register (.imm (wordOffset maxStackAlloc)))))
      (upshift register (count - maxStackAlloc))
termination_by count
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Literal immediate Sub recursion, including the zero-count instruction. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "downshift_def"
  (words_as_type_indexed_bitvec)]
def downshift {width : Nat} [NeZero width] (register count : Nat) : HolProg width :=
  if count ≤ maxStackAlloc then
    .inst (.arith (.binop .sub register register (.imm (wordOffset count))))
  else
    .seq (.inst (.arith (.binop .sub register register (.imm (wordOffset maxStackAlloc)))))
      (downshift register (count - maxStackAlloc))
termination_by count
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Preserve HOL's nested Seq and restore the address register after Store. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "stack_store_def"
  (words_as_type_indexed_bitvec)]
def stackStore {width : Nat} [NeZero width] (address register count : Nat) : HolProg width :=
  .seq (upshift address count)
    (.seq (.inst (.mem .store register (.addr address 0))) (downshift address count))

/-- Load through the shifted destination itself, without a restoring shift. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "stack_load_def"
  (words_as_type_indexed_bitvec)]
def stackLoad {width : Nat} [NeZero width] (register count : Nat) : HolProg width :=
  .seq (upshift register count) (.inst (.mem .load register (.addr register 0)))

/-- Flapjack equation fixture preserving the complete source recursion. -/
theorem upshift_large {width : Nat} [NeZero width] (register count : Nat)
    (large : maxStackAlloc < count) :
    upshift (width := width) register count =
      .seq (.inst (.arith (.binop .add register register (.imm (wordOffset maxStackAlloc)))))
        (upshift register (count - maxStackAlloc)) := by
  rw [upshift, if_neg (Nat.not_le.mpr large)]

/-- Flapjack equation fixture preserving the complete source recursion. -/
theorem downshift_large {width : Nat} [NeZero width] (register count : Nat)
    (large : maxStackAlloc < count) :
    downshift (width := width) register count =
      .seq (.inst (.arith (.binop .sub register register (.imm (wordOffset maxStackAlloc)))))
        (downshift register (count - maxStackAlloc)) := by
  rw [downshift, if_neg (Nat.not_le.mpr large)]

end Flapjack.Compiler.Backend.StackRemove
