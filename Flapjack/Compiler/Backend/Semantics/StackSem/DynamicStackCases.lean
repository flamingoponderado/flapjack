import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.BackendCommon

/-! Source-shaped dynamic-index StackSem evaluator fragments. These are
untagged assembly infrastructure: HOL's total evaluate_def remains unfinished.
The shifted-word roundtrip is HOL's alignment test, including narrow widths. -/
namespace Flapjack.StackSemDynamicStackCases
open StackSemStateOps

/-- StackLoadAny reads its offset before updating the destination register. -/
def stackLoadAny {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else match getVar rn s with
    | some (.word w) =>
      let shifted := w >>> wordShiftAmount width
      let i := s.stackSpace + shifted.toNat
      if h : i < s.stack.length ∧ shifted <<< wordShiftAmount width = w then
        (none, setVar r (s.stack[i]'h.1) s)
      else (some .error, emptyEnv s)
    | _ => (some .error, emptyEnv s)

/-- StackStoreAny reads both registers in the original state, retaining Loc
payloads and checking bounds and alignment before the list update. -/
def stackStoreAny {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else match getVar r s, getVar rn s with
    | some value, some (.word w) =>
      let shifted := w >>> wordShiftAmount width
      let i := s.stackSpace + shifted.toNat
      if i < s.stack.length ∧ shifted <<< wordShiftAmount width = w then
        (none, { s with stack := s.stack.set i value })
      else (some .error, emptyEnv s)
    | _, _ => (some .error, emptyEnv s)

/-- Flapjack assembly certificate: both cases preserve the source clock in
every branch, including disabled stack operations and environment cleanup. -/
theorem dynamicStackCases_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (s : StackSemStateFiniteExact width C F) :
    (stackLoadAny r rn s).2.clock = s.clock ∧
    (stackStoreAny r rn s).2.clock = s.clock := by
  constructor
  all_goals simp only [stackLoadAny, stackStoreAny]
  all_goals repeat' split
  all_goals rfl

/-- Flapjack frame certificate: error cleanup and successful accesses leave
memory and stack-space unchanged, at every positive word width. -/
theorem dynamicStackCases_frame {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (s : StackSemStateFiniteExact width C F) :
    (stackLoadAny r rn s).2.memory = s.memory ∧
    (stackStoreAny r rn s).2.memory = s.memory ∧
    (stackLoadAny r rn s).2.stackSpace = s.stackSpace ∧
    (stackStoreAny r rn s).2.stackSpace = s.stackSpace := by
  simp only [stackLoadAny, stackStoreAny]
  repeat' constructor
  all_goals repeat' split
  all_goals rfl

/-- Flapjack boundary certificate: a successful dynamic store preserves the
original register reads, exact payload and source list-update index. -/
theorem stackStoreAny_success {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (s : StackSemStateFiniteExact width C F)
    (value : WordLocW width) (w : BitVec width)
    (hUse : s.useStack = true) (hValue : getVar r s = some value)
    (hOffset : getVar rn s = some (.word w))
    (hBound : s.stackSpace + (w >>> wordShiftAmount width).toNat < s.stack.length)
    (hAligned : (w >>> wordShiftAmount width) <<< wordShiftAmount width = w) :
    stackStoreAny r rn s = (none, { s with
      stack := s.stack.set (s.stackSpace + (w >>> wordShiftAmount width).toNat) value }) := by
  simp only [stackStoreAny, hUse, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hValue, hOffset, hBound, hAligned, and_self]

/-- Flapjack boundary certificate: an enabled load with an unaligned Word
offset clears the environment, even when its shifted index is in bounds. -/
theorem stackLoadAny_unaligned {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (s : StackSemStateFiniteExact width C F) (w : BitVec width)
    (hUse : s.useStack = true) (hOffset : getVar rn s = some (.word w))
    (hAligned : (w >>> wordShiftAmount width) <<< wordShiftAmount width ≠ w) :
    stackLoadAny r rn s = (some .error, emptyEnv s) := by
  simp [stackLoadAny, hUse, hOffset, hAligned]

end Flapjack.StackSemDynamicStackCases
