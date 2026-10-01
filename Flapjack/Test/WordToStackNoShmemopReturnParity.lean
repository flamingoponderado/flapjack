import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopReturn

namespace Flapjack.Test.WordToStackNoShmemopReturnParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- cr_0_safe
example : let p : HolProg 1 := .skip;
    (noShmemop (copyRetNative false false (0, 999, "frame") ([] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_0_forbidden
example : let p : HolProg 1 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative false false (0, 999, "frame") ([] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_1_safe
example : let p : HolProg 32 := .skip;
    (noShmemop (copyRetNative true false (1, 999, "frame") ([] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_1_forbidden
example : let p : HolProg 32 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative true false (1, 999, "frame") ([] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_2_safe
example : let p : HolProg 64 := .skip;
    (noShmemop (copyRetNative false true (9, 999, "frame") ([true, false, true] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_2_forbidden
example : let p : HolProg 64 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative false true (9, 999, "frame") ([true, false, true] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_3_safe
example : let p : HolProg 80 := .skip;
    (noShmemop (copyRetNative true true (0, 999, "frame") ([true, false, true, false] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_3_forbidden
example : let p : HolProg 80 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative true true (0, 999, "frame") ([true, false, true, false] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_4_safe
example : let p : HolProg 64 := .skip;
    (noShmemop (copyRetNative false false (2, 999, "frame") ([true, false, true] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_4_forbidden
example : let p : HolProg 64 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative false false (2, 999, "frame") ([true, false, true] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_5_safe
example : let p : HolProg 32 := .skip;
    (noShmemop (copyRetNative true false (3, 999, "frame") ([true, false, true, false, true] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_5_forbidden
example : let p : HolProg 32 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative true false (3, 999, "frame") ([true, false, true, false, true] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_6_safe
example : let p : HolProg 1 := .skip;
    (noShmemop (copyRetNative false true (0, 999, "frame") ([true, false] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_6_forbidden
example : let p : HolProg 1 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative false true (0, 999, "frame") ([true, false] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- cr_7_safe
example : let p : HolProg 80 := .skip;
    (noShmemop (copyRetNative true true (1, 999, "frame") ([true, false, true, false, true, false] : List Bool) p),
      noShmemop p) = (true, true) := rfl

-- cr_7_forbidden
example : let p : HolProg 80 := .shMemOp .load 0 (.addr 1 0);
    (noShmemop (copyRetNative true true (1, 999, "frame") ([true, false, true, false, true, false] : List Bool) p),
      noShmemop p) = (false, false) := rfl

-- Independent carriers and arbitrary positive width, with no safety premise.
example {width : Nat} [NeZero width] {β γ : Type}
    (perf handler : Bool) (frame : Nat × Nat × γ) (values : List β)
    (kont : HolProg width) :
    noShmemop (copyRetNative perf handler frame values kont) = noShmemop kont :=
  copyRetNoShmemop perf handler frame values kont

end Flapjack.Test.WordToStackNoShmemopReturnParity
