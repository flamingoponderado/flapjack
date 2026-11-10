module

public import Flapjack.Pancake.Proofs.PanGlobals

@[expose] public section

/-!
# `compile_top` production-route agreement

The fixed-width production wrapper agrees with the generic entry function.
-/

namespace Flapjack.Test.PanGlobalsCompileTopShapeWfParity

open Flapjack

example {width : Nat} [NeZero width] (declarations : List (Decl (BitVec width)))
    (start : FunName) :
    globalCompileTopCake declarations start =
      globalCompileTopForStart (BitVec.ofNat width (width / 8))
        (BitVec.ofNat width) declarations start := by
  rw [globalCompileTopCake_eq]
  simp only [cakeBytesInWord]

end Flapjack.Test.PanGlobalsCompileTopShapeWfParity
