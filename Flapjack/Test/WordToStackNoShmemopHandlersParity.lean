import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop.Handlers

namespace Flapjack.Test.WordToStackNoShmemopHandlersParity
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- Actual theorem applications at all original independent carriers and inputs.
example {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (l1 l2 : Nat) (frame : Nat × β × γ) :
    noShmemop (pushHandlerNative (width := width) perf l1 l2 frame) = true :=
  pushHandlerNoShmemop perf l1 l2 frame
example {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (frame : Nat × β × γ) (program : HolProg width) :
    noShmemop (popHandlerNative perf frame program) = noShmemop program :=
  popHandlerNoShmemop perf frame program
example {width : Nat} [NeZero width] {α β : Type}
    (perf : Bool) (destination : Sum α β) (count : Nat) (frame : Nat × Nat × Nat) :
    noShmemop (stackHandlerArgsNative (width := width) perf destination count frame) = true :=
  stackHandlerArgsNoShmemop perf destination count frame

-- Sixteen same-input fresh original observations, including false continuations.
example : noShmemop (pushHandlerNative false 7 9 (2,true,"ignored") : HolProg 64) = true := by decide +kernel
example : (noShmemop (popHandlerNative false (2,true,"ignored") (.skip) : HolProg 64), noShmemop (.skip : HolProg 64)) = (true,true) := by decide +kernel
example : (noShmemop (popHandlerNative false (2,true,"ignored") (.shMemOp .load 0 (.addr 1 0)) : HolProg 64), noShmemop (.shMemOp .load 0 (.addr 1 0) : HolProg 64)) = (false,false) := by decide +kernel
example : noShmemop (pushHandlerNative true 7 9 (2,true,"ignored") : HolProg 64) = true := by decide +kernel
example : (noShmemop (popHandlerNative true (2,true,"ignored") (.skip) : HolProg 64), noShmemop (.skip : HolProg 64)) = (true,true) := by decide +kernel
example : (noShmemop (popHandlerNative true (2,true,"ignored") (.shMemOp .load 0 (.addr 1 0)) : HolProg 64), noShmemop (.shMemOp .load 0 (.addr 1 0) : HolProg 64)) = (false,false) := by decide +kernel
example : noShmemop (pushHandlerNative false 7 9 (0,([1,2,3] : List Nat),false) : HolProg 1) = true := by decide +kernel
example : (noShmemop (popHandlerNative false (0,([1,2,3] : List Nat),false) (.skip) : HolProg 1), noShmemop (.skip : HolProg 1)) = (true,true) := by decide +kernel
example : (noShmemop (popHandlerNative false (0,([1,2,3] : List Nat),false) (.shMemOp .load 0 (.addr 1 0)) : HolProg 1), noShmemop (.shMemOp .load 0 (.addr 1 0) : HolProg 1)) = (false,false) := by decide +kernel
example : noShmemop (pushHandlerNative true 7 9 (0,([1,2,3] : List Nat),false) : HolProg 1) = true := by decide +kernel
example : (noShmemop (popHandlerNative true (0,([1,2,3] : List Nat),false) (.skip) : HolProg 1), noShmemop (.skip : HolProg 1)) = (true,true) := by decide +kernel
example : (noShmemop (popHandlerNative true (0,([1,2,3] : List Nat),false) (.shMemOp .load 0 (.addr 1 0)) : HolProg 1), noShmemop (.shMemOp .load 0 (.addr 1 0) : HolProg 1)) = (false,false) := by decide +kernel
example : noShmemop (stackHandlerArgsNative false (Sum.inl true : Sum Bool Unit) 0 (0,0,0) : HolProg 32) = true := by decide +kernel
example : noShmemop (stackHandlerArgsNative true (Sum.inl true : Sum Bool Unit) 7 (2,3,4) : HolProg 64) = true := by decide +kernel
example : noShmemop (stackHandlerArgsNative false (Sum.inr () : Sum Bool Unit) 9 (0,0,0) : HolProg 1) = true := by decide +kernel
example : noShmemop (stackHandlerArgsNative true (Sum.inr () : Sum Bool Unit) 5 (0,1208925819614629174706176,1208925819614629174706179) : HolProg 80) = true := by decide +kernel

end Flapjack.Test.WordToStackNoShmemopHandlersParity
