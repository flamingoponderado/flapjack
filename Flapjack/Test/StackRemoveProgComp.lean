import Flapjack.Compiler.Backend.StackRemove.ProgComp

/-! Generic native wrapper fixtures; Flapjack infrastructure rather than new HOL ports. -/

namespace Flapjack.Test.StackRemoveProgComp

open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

-- wrapper_1_bool
example : progComp (width := 1) true (0, 0) 24 (true, .stackFree 256) =
    (true, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_1_list
example : progComp (width := 1) true (0, 0) 24 (([true, false] : List Bool), .stackFree 256) =
    (([true, false] : List Bool), stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_1_nat
example : progComp (width := 1) true (0, 0) 24 (1234, .stackFree 256) =
    (1234, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_8_bool
example : progComp (width := 8) true (0, 0) 24 (true, .stackFree 256) =
    (true, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_8_list
example : progComp (width := 8) true (0, 0) 24 (([true, false] : List Bool), .stackFree 256) =
    (([true, false] : List Bool), stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_8_nat
example : progComp (width := 8) true (0, 0) 24 (1234, .stackFree 256) =
    (1234, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_32_bool
example : progComp (width := 32) true (0, 0) 24 (true, .stackFree 256) =
    (true, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_32_list
example : progComp (width := 32) true (0, 0) 24 (([true, false] : List Bool), .stackFree 256) =
    (([true, false] : List Bool), stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_32_nat
example : progComp (width := 32) true (0, 0) 24 (1234, .stackFree 256) =
    (1234, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_64_bool
example : progComp (width := 64) true (0, 0) 24 (true, .stackFree 256) =
    (true, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_64_list
example : progComp (width := 64) true (0, 0) 24 (([true, false] : List Bool), .stackFree 256) =
    (([true, false] : List Bool), stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_64_nat
example : progComp (width := 64) true (0, 0) 24 (1234, .stackFree 256) =
    (1234, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_80_bool
example : progComp (width := 80) true (0, 0) 24 (true, .stackFree 256) =
    (true, stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_80_list
example : progComp (width := 80) true (0, 0) 24 (([true, false] : List Bool), .stackFree 256) =
    (([true, false] : List Bool), stackFree 24 256) := by
  simp only [progComp, comp]

-- wrapper_80_nat
example : progComp (width := 80) true (0, 0) 24 (1234, .stackFree 256) =
    (1234, stackFree 24 256) := by
  simp only [progComp, comp]

-- Unconditional arbitrary independent carrier and configuration, no output/run premise.

example {width : Nat} [NeZero width] {Name : Type} (name : Name) (p : HolProg width)
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat) :
    progComp jump bounds pointer (name, p) = (name, comp jump bounds pointer p) := by rfl

example {width : Nat} [NeZero width] {Name : Type} (entry : Name × HolProg width)
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat) :
    (progComp jump bounds pointer entry).1 = entry.1 := by rfl

end Flapjack.Test.StackRemoveProgComp
