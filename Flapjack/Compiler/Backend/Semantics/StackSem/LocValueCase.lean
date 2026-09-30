import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels

/-! Source-shaped LocValue evaluator fragment. This is untagged assembly
infrastructure until the total HOL evaluator is assembled. The canonical
label predicate is retained without a decidability or membership premise. -/
namespace Flapjack.StackSemLocValueCase
open StackSemStateOps

/-- LocValue preserves the entire state when the source label check fails. -/
noncomputable def locValue {width : Nat} [NeZero width] {C F : Type}
    (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F := by
  classical
  exact if StackSem.locCheckExact s.code (l1, l2) then
    (none, setVar r (.loc l1 l2) s) else (some .error, s)

/-- Flapjack assembly certificate: LocValue always preserves the clock. -/
theorem locValue_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F) :
    (locValue r l1 l2 s).2.clock = s.clock := by
  classical
  simp only [locValue]
  split <;> rfl

/-- Flapjack assembly certificate: failure has exactly HOL's unchanged state. -/
theorem locValue_failure {width : Nat} [NeZero width] {C F : Type}
    (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F)
    (h : ¬ StackSem.locCheckExact s.code (l1, l2)) :
    locValue r l1 l2 s = (some .error, s) := by
  classical
  simp [locValue, h]

/-- Flapjack assembly certificate: successful label checks update exactly the
destination register with the original pair of location components. -/
theorem locValue_success {width : Nat} [NeZero width] {C F : Type}
    (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F)
    (h : StackSem.locCheckExact s.code (l1, l2)) :
    locValue r l1 l2 s = (none, setVar r (.loc l1 l2) s) := by
  classical
  simp [locValue, h]

/-- Flapjack frame certificate: both source branches preserve code, memory,
the stack, stack-space, and stack-enable flag. Failure clears no environment. -/
theorem locValue_frame {width : Nat} [NeZero width] {C F : Type}
    (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F) :
    (locValue r l1 l2 s).2.code = s.code ∧
    (locValue r l1 l2 s).2.memory = s.memory ∧
    (locValue r l1 l2 s).2.stack = s.stack ∧
    (locValue r l1 l2 s).2.stackSpace = s.stackSpace ∧
    (locValue r l1 l2 s).2.useStack = s.useStack := by
  classical
  simp only [locValue]
  repeat' constructor
  all_goals split <;> rfl

end Flapjack.StackSemLocValueCase
