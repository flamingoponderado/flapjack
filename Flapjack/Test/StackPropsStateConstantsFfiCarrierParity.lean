import Flapjack.Compiler.Backend.StackProps.StateConstants

/-! Generic kernel fixtures for the original independently typed FFI update.
No HOL declaration is duplicated here; these exercise the corrected published
full conjunction over arbitrary positive machine width and independent hosts. -/
open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackProps

example {width : Nat} [NeZero width] {C F OtherF : Type}
    (x : Nat) (y : WordLocW width) (z : StackSemStateFiniteExact width C F)
    (k : HolFfiState OtherF) :
    setVar x y ({ z with ffi := k } : StackSemStateFiniteExact width C OtherF) =
      { setVar x y z with ffi := k } :=
  (setVarWithConst x y z 0 z.memory k [] 0).2.2.1

example (z : StackSemStateFiniteExact 1 Unit Unit) (k : HolFfiState Bool) :
    setVar 0 (.word 1) ({ z with ffi := k } : StackSemStateFiniteExact 1 Unit Bool) =
      { setVar 0 (.word 1) z with ffi := k } :=
  (setVarWithConst 0 (.word 1) z 0 z.memory k [] 0).2.2.1
