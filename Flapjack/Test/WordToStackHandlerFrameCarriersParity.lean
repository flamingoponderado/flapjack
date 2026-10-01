import Flapjack.Compiler.Backend.WordToStack.NativeHandlers

/-! Complete output equality observations from original HOL over heterogeneous
unused frame carriers. These are regressions, not cross-language equivalence. -/
namespace Flapjack.Test.WordToStackHandlerFrameCarriersParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

-- hcf_push_64_F
example : (pushHandlerNative false 7 9 (2,true,"ignored") : HolProg 64) = pushHandlerNative false 7 9 (2,0,0) := rfl

-- hcf_pop_64_F_skip
example : (popHandlerNative false (2,true,"ignored") (.skip) : HolProg 64) = popHandlerNative false (2,0,0) (.skip) := rfl

-- hcf_pop_64_F_forbidden
example : (popHandlerNative false (2,true,"ignored") (.shMemOp .load 0 (.addr 1 0)) : HolProg 64) = popHandlerNative false (2,0,0) (.shMemOp .load 0 (.addr 1 0)) := rfl

-- hcf_push_64_T
example : (pushHandlerNative true 7 9 (2,true,"ignored") : HolProg 64) = pushHandlerNative true 7 9 (2,0,0) := rfl

-- hcf_pop_64_T_skip
example : (popHandlerNative true (2,true,"ignored") (.skip) : HolProg 64) = popHandlerNative true (2,0,0) (.skip) := rfl

-- hcf_pop_64_T_forbidden
example : (popHandlerNative true (2,true,"ignored") (.shMemOp .load 0 (.addr 1 0)) : HolProg 64) = popHandlerNative true (2,0,0) (.shMemOp .load 0 (.addr 1 0)) := rfl

-- hcf_push_1_F
example : (pushHandlerNative false 7 9 (0,([1,2,3] : List Nat),false) : HolProg 1) = pushHandlerNative false 7 9 (0,0,0) := rfl

-- hcf_pop_1_F_skip
example : (popHandlerNative false (0,([1,2,3] : List Nat),false) (.skip) : HolProg 1) = popHandlerNative false (0,0,0) (.skip) := rfl

-- hcf_pop_1_F_forbidden
example : (popHandlerNative false (0,([1,2,3] : List Nat),false) (.shMemOp .load 0 (.addr 1 0)) : HolProg 1) = popHandlerNative false (0,0,0) (.shMemOp .load 0 (.addr 1 0)) := rfl

-- hcf_push_1_T
example : (pushHandlerNative true 7 9 (0,([1,2,3] : List Nat),false) : HolProg 1) = pushHandlerNative true 7 9 (0,0,0) := rfl

-- hcf_pop_1_T_skip
example : (popHandlerNative true (0,([1,2,3] : List Nat),false) (.skip) : HolProg 1) = popHandlerNative true (0,0,0) (.skip) := rfl

-- hcf_pop_1_T_forbidden
example : (popHandlerNative true (0,([1,2,3] : List Nat),false) (.shMemOp .load 0 (.addr 1 0)) : HolProg 1) = popHandlerNative true (0,0,0) (.shMemOp .load 0 (.addr 1 0)) := rfl

-- Unrestricted carrier and continuation applications, matching both HOL types.
example {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    toGeneric (pushHandlerNative (width := width) perf l1 l2 kf) =
      Flapjack.Compiler.Backend.WordToStackRegFormat.pushHandlerW perf l1 l2 kf :=
  toGeneric_pushHandlerNative perf l1 l2 kf

example {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (kf : Nat × β × γ) (prog : HolProg width) :
    toGeneric (popHandlerNative perf kf prog) =
      Flapjack.Compiler.Backend.WordToStackRegFormat.popHandler perf kf (toGeneric prog) :=
  toGeneric_popHandlerNative perf kf prog

end Flapjack.Test.WordToStackHandlerFrameCarriersParity
