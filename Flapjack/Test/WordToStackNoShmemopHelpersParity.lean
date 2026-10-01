import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers

/-! Same-input original helper observations; regression evidence only. -/
namespace Flapjack.Test.WordToStackNoShmemopHelpersParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- nsh_move_empty
example : noShmemop (wMoveAuxNative [] (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_move_rr
example : noShmemop (wMoveAuxNative [(.inl 0,.inl 1)] (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_move_rs
example : noShmemop (wMoveAuxNative [(.inl 0,.inr 99)] (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_move_sr
example : noShmemop (wMoveAuxNative [(.inr 99,.inl 1)] (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_move_ss
example : noShmemop (wMoveAuxNative [(.inr 99,.inr 88)] (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_move_multi
example : noShmemop (wMoveAuxNative [(.inl 0,.inr 9),(.inr 8,.inl 1),(.inr 7,.inr 6)] (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_move_width1
example : noShmemop (wMoveAuxNative [(.inr 999,.inr 888)] (0,0,999) : HolProg 1) = true := by
  rfl

-- nsh_load_empty
example : noShmemop (wStackLoadNative [] .skip : HolProg 64) = true := by
  rfl

-- nsh_load_loads
example : noShmemop (wStackLoadNative [(1,0),(9,999)] .tick : HolProg 64) = true := by
  rfl

-- nsh_load_forbidden
example : noShmemop (wStackLoadNative [(1,0),(9,999)] (.shMemOp .load 0 (.addr 1 0)) : HolProg 64) = false := by
  rfl

-- nsh_write1_register
example : noShmemop (wRegWrite1Native (fun _ => .skip) 0 (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_write1_stack
example : noShmemop (wRegWrite1Native (fun _ => .tick) 999 (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_write1_forbidden
example : noShmemop (wRegWrite1Native (fun _ => .shMemOp .load 0 (.addr 1 0)) 999 (2,0,99) : HolProg 64) = false := by
  rfl

-- nsh_write2_register
example : noShmemop (wRegWrite2Native (fun _ => .skip) 0 (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_write2_stack
example : noShmemop (wRegWrite2Native (fun _ => .tick) 999 (2,0,99) : HolProg 64) = true := by
  rfl

-- nsh_write2_forbidden
example : noShmemop (wRegWrite2Native (fun _ => .shMemOp .load 0 (.addr 1 0)) 999 (2,0,99) : HolProg 64) = false := by
  rfl

-- nsh_live_zero
example : noShmemop ((wLiveNative (.ln,.ln) (.list [],17) (0,0,999)).1 : HolProg 64) = true := by
  rfl

-- nsh_live_nonzero
example : noShmemop ((wLiveNative (.ln,.ln) (.list [],17) (2,3,5)).1 : HolProg 64) = true := by
  rfl

-- nsh_live_width1
example : noShmemop ((wLiveNative (.ln,.ln) (.list [],17) (0,1,999)).1 : HolProg 1) = true := by
  rfl

-- nsh_stack_zero
example : noShmemop (stackMoveNative 0 999 0 77 (.shMemOp .load 0 (.addr 1 0)) : HolProg 64) = false := by
  rfl

-- nsh_stack_positive
example : noShmemop (stackMoveNative 4 999 0 77 (.skip) : HolProg 64) = true := by
  rfl

-- nsh_stack_forbidden
example : noShmemop (stackMoveNative 4 999 0 77 (.shMemOp .load 0 (.addr 1 0)) : HolProg 64) = false := by
  rfl

-- Unrestricted public theorem applications retain the source hypotheses.
example {width : Nat} [NeZero width] (moves : List (Sum Nat Nat × Sum Nat Nat))
    (kf : Nat × Nat × Nat) : noShmemop (wMoveAuxNative (width := width) moves kf) = true :=
  wMoveAuxNoShmemop moves kf

example {width : Nat} [NeZero width] (prog : Nat → HolProg width)
    (r : Nat) (kf : Nat × Nat × Nat) (h : ∀ reg, noShmemop (prog reg) = true) :
    noShmemop (wRegWrite1Native prog r kf) = true ∧
    noShmemop (wRegWrite2Native prog r kf) = true :=
  ⟨wRegWrite1NoShmemop prog r kf h, wRegWrite2NoShmemop prog r kf h⟩

end Flapjack.Test.WordToStackNoShmemopHelpersParity
