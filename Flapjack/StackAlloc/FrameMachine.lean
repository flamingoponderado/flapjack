module

public import Flapjack.StackAlloc.Correctness
public import Flapjack.RiscV.PanMemory

@[expose] public section

/-!
# Bounded StackLang frame semantics

CakeML's StackLang state distinguishes the stack array from `stack_space`, the
number of free words at the front of the current frame.  The first executable
StackAlloc machine model intentionally used an unbounded stack function for
the collector body.  This module adds the bounded frame boundary needed by
the general StackLang semantics without changing that small collector model.

The evaluator is fuel-bounded and keeps unsupported calls explicit.  Its
frame operations follow the equations in `cakeml/compiler/backend/semantics/
stackSemScript.sml`: fixed and dynamic accesses are bounds-checked, dynamic
offsets must be word-aligned, and bitmap loads read a separate bitmap table.
-/

namespace Flapjack.RiscV

def stackFrameAnyOffset [NeZero width] (value : Word width) : Option Nat :=
  let offset := BitVec.ushiftRight value 3
  if BitVec.shiftLeft offset 3 == value then some offset.toNat else none

def stackFrameBitmapAt : List (Word width) → Nat → Option (Word width)
  | [], _ => none
  | bitmap :: _, 0 => some bitmap
  | _ :: bitmaps, index + 1 => stackFrameBitmapAt bitmaps index

/-! The preceding call equations expose the two leaf cases directly.  These
    variants retain the callee's evaluated state and therefore compose with a
    callee containing sequences or FFI actions. -/

theorem stackFrameAnyOffset_eq_toNat [NeZero width]
    (value : Word width) (offset : Nat)
    (h : stackFrameAnyOffset value = some offset) :
    offset = (BitVec.ushiftRight value 3).toNat := by
  simp [stackFrameAnyOffset] at h
  exact h.2.symm

end Flapjack.RiscV
