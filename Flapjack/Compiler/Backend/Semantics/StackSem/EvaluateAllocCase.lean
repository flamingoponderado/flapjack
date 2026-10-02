import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation

/-! A source-shaped `evaluate_def` Alloc case fragment over the exact
StackSem state/result carriers. It is deliberately untagged: this partial case
helper is not the total HOL `evaluate_def` definition. The total evaluator is assembled in Evaluate.lean; this fragment
retains its separate, nonrecursive interface. -/

namespace Flapjack.StackSemEvaluateAlloc

/-- The HOL `evaluate (Alloc n, s)` branch: enforce `use_alloc`, read a Word
register, then invoke the exact StackSem allocation transition. Every rejected
guard returns `Error` with the original state. -/
def evaluateAllocCase {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (state : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if !state.useAlloc then
    (some .error, state)
  else
    match StackSemStateOps.getVar register state with
    | some (.word words) => StackSemAllocation.alloc words state
    | _ => (some .error, state)

theorem evaluateAllocCase_disabled {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (state : StackSemStateFiniteExact width C F)
    (h : state.useAlloc = false) :
    evaluateAllocCase register state = (some .error, state) := by
  simp [evaluateAllocCase, h]

theorem evaluateAllocCase_missing {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (state : StackSemStateFiniteExact width C F)
    (hUse : state.useAlloc = true) (hReg : state.regs.lookup register = none) :
    evaluateAllocCase register state = (some .error, state) := by
  simp [evaluateAllocCase, hUse, StackSemStateOps.getVar, hReg]

theorem evaluateAllocCase_location {width : Nat} [NeZero width] {C F : Type}
    (register label offset : Nat) (state : StackSemStateFiniteExact width C F)
    (hUse : state.useAlloc = true)
    (hReg : state.regs.lookup register = some (.loc label offset)) :
    evaluateAllocCase register state = (some .error, state) := by
  simp [evaluateAllocCase, hUse, StackSemStateOps.getVar, hReg]

theorem evaluateAllocCase_word {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (words : BitVec width) (state : StackSemStateFiniteExact width C F)
    (hUse : state.useAlloc = true)
    (hReg : state.regs.lookup register = some (.word words)) :
    evaluateAllocCase register state = StackSemAllocation.alloc words state := by
  simp [evaluateAllocCase, hUse, StackSemStateOps.getVar, hReg]

/-- Flapjack factoring: the reviewed GC record update preserves clock. -/
theorem gc_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (state collected : StackSemStateFiniteExact width C F)
    (h : StackSemAllocation.gc state = some collected) : collected.clock = state.clock := by
  simp only [StackSemAllocation.gc] at h
  all_goals repeat' (split at h)
  all_goals try contradiction
  all_goals cases h
  all_goals rfl

/-- Flapjack factoring: every reviewed allocation result preserves clock. -/
theorem alloc_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (words : BitVec width) (state : StackSemStateFiniteExact width C F) :
    (StackSemAllocation.alloc words state).2.clock = state.clock := by
  cases h : StackSemAllocation.gc (StackSemStateOps.setStore .allocSize (.word words) state) with
  | none => simp only [StackSemAllocation.alloc, h]
  | some collected =>
      have hc := gc_clock_eq _ _ h
      simp only [StackSemAllocation.alloc, h]
      all_goals repeat' split
      all_goals exact hc

/-- Flapjack assembly certificate: allocation preserves the clock on every
success and failure path. The GC oracle changes roots/memory/store only. -/
theorem evaluateAllocCase_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (state : StackSemStateFiniteExact width C F) :
    (evaluateAllocCase register state).2.clock = state.clock := by
  simp only [evaluateAllocCase]
  all_goals repeat' split
  all_goals first | rfl | exact alloc_clock_eq _ _

end Flapjack.StackSemEvaluateAlloc
