import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Source-shaped fixed-index StackSem evaluator fragments. These helpers are
untagged because they are individual cases, not HOL's total evaluate_def.
Full evaluator assembly remains on the fleet dependency graph. -/
namespace Flapjack.StackSemFixedStackCases
open StackSemStateOps

/-- HOL StackAlloc case, including the Word 2 halt and environment cleanup. -/
def stackAlloc {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else if s.stackSpace < n then
    (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv s)
  else (none, { s with stackSpace := s.stackSpace - n })

/-- HOL StackFree case; an excessive free clears the environment. -/
def stackFree {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else if s.stack.length < s.stackSpace + n then (some .error, emptyEnv s)
  else (none, { s with stackSpace := s.stackSpace + n })

/-- HOL StackLoad case; Word and Loc values are transferred unchanged. -/
def stackLoad {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else if h : s.stackSpace + n < s.stack.length then
    (none, setVar r s.stack[s.stackSpace + n] s)
  else (some .error, emptyEnv s)

/-- HOL StackStore case, with bounds checked before register lookup. -/
def stackStore {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else if s.stack.length ≤ s.stackSpace + n then (some .error, emptyEnv s)
  else match getVar r s with
    | none => (some .error, emptyEnv s)
    | some value => (none, { s with stack := s.stack.set (s.stackSpace + n) value })

/-- HOL StackGetSize case; conversion to Word is modular at the state width. -/
def stackGetSize {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !s.useStack then (some .error, s)
  else (none, setVar r (.word (BitVec.ofNat width s.stackSpace)) s)

/-- Flapjack assembly certificate: each fixed stack case preserves clock,
including every disabled, bounds, exhaustion and missing-register branch. -/
theorem fixedStackCases_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (s : StackSemStateFiniteExact width C F) :
    (stackAlloc n s).2.clock = s.clock ∧
    (stackFree n s).2.clock = s.clock ∧
    (stackLoad r n s).2.clock = s.clock ∧
    (stackStore r n s).2.clock = s.clock ∧
    (stackGetSize r s).2.clock = s.clock := by
  simp only [stackAlloc, stackFree, stackLoad, stackStore, stackGetSize]
  repeat' constructor
  all_goals repeat' split
  all_goals rfl

/-- Flapjack boundary certificate: allocation exhaustion clears exactly the
HOL environment and returns the width-indexed Word 2 halt. -/
theorem stackAlloc_exhausted {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : StackSemStateFiniteExact width C F)
    (hUse : s.useStack = true) (hSpace : s.stackSpace < n) :
    stackAlloc n s = (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv s) := by
  simp [stackAlloc, hUse, hSpace]

/-- Flapjack boundary certificate: equality at the free-space limit succeeds. -/
theorem stackFree_at_boundary {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : StackSemStateFiniteExact width C F)
    (hUse : s.useStack = true) (hSpace : s.stackSpace + n = s.stack.length) :
    stackFree n s = (none, { s with stackSpace := s.stack.length }) := by
  simp [stackFree, hUse, hSpace]

/-- Flapjack assembly certificate: stack transitions never modify memory,
even when they clear the register/stack environment on error. -/
theorem fixedStackCases_memory_eq {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (s : StackSemStateFiniteExact width C F) :
    (stackAlloc n s).2.memory = s.memory ∧
    (stackFree n s).2.memory = s.memory ∧
    (stackLoad r n s).2.memory = s.memory ∧
    (stackStore r n s).2.memory = s.memory ∧
    (stackGetSize r s).2.memory = s.memory := by
  simp only [stackAlloc, stackFree, stackLoad, stackStore, stackGetSize]
  repeat' constructor
  all_goals repeat' split
  all_goals rfl

/-- Flapjack successful store certificate, retaining the exact Word or Loc
payload and all other state fields. Bounds precede the register read. -/
theorem stackStore_success {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (value : WordLocW width) (s : StackSemStateFiniteExact width C F)
    (hUse : s.useStack = true) (hBound : s.stackSpace + n < s.stack.length)
    (hReg : s.regs.lookup r = some value) :
    stackStore r n s = (none, { s with stack := s.stack.set (s.stackSpace + n) value }) := by
  simp [stackStore, hUse, Nat.not_le_of_lt hBound, getVar, hReg]

/-- Flapjack exact end-boundary certificate: a load at the list length fails
and clears the environment, rather than returning an arbitrary list element. -/
theorem stackLoad_at_boundary {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (s : StackSemStateFiniteExact width C F)
    (hUse : s.useStack = true) (hBound : s.stackSpace + n = s.stack.length) :
    stackLoad r n s = (some .error, emptyEnv s) := by
  simp [stackLoad, hUse, hBound]

end Flapjack.StackSemFixedStackCases
