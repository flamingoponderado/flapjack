module

public import Flapjack.Stack

@[expose] public section

/-!
# LabLang

LabLang is CakeML's target-neutral, labelled assembly layer.  This is the
structured-to-flat portion of `stack_to_labScript.sml`: StackLang control
flow is flattened into labels and jumps, while target instruction encoding is
left to the RISC-V backend.
-/

namespace Flapjack

structure LabRef where
  sectionId : Nat
  label : Nat
  deriving DecidableEq, Repr

inductive LabAsm (α : Type u) where
  | jump (target : LabRef)
  | jumpCmp (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (target : LabRef)
  | call (target : LabRef)
  | locValue (register : Nat) (target : LabRef)
  | linkValue (target : LabRef)
  | return (register : Nat)
  | callFfi (function : FunName)
  | heapAlloc (words : Nat)
  | install
  | halt
  deriving Repr

inductive LabJump where
  | direct (target : LabRef)
  | register (register : Nat)
  deriving DecidableEq, Repr

def labFindLabel (label : Nat) : List Nat → Nat
  | [] => 0
  | candidate :: labels =>
      match label with
      | 0 => candidate
      | label + 1 => labFindLabel label labels

def labNegateCmp : Cmp → Cmp
  | .less => .notLess
  | .equal => .notEqual
  | .lower => .notLower
  | .test => .notTest
  | .notLess => .less
  | .notEqual => .equal
  | .notLower => .lower
  | .notTest => .test

end Flapjack
