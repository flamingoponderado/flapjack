import Flapjack.Compiler.Backend.StackProps.AllocationConstants
import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock
namespace Flapjack.StackSemClock
open Flapjack StackSemAllocation StackSemStoreConsts StackSemInst StackSemShMem
/-- Canonical imported state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original GC clock inequality, for the actual native GC operation. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "gc_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcClock {width : Nat} [NeZero width] {C F : Type}
    (source target : StackSemStateFiniteExact width C F)
    (execution : gc source = some target) : target.clock ≤ source.clock := by
  simp only [gc] at execution
  repeat' first | split at execution | cases execution | simp_all
/-- The original unused universal xs binder is retained at an arbitrary type. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "alloc_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocClock {width : Nat} [NeZero width] {C F U : Type}
    (word : BitVec width) (_xs : U) (source target : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : alloc word source = (result,target)) : target.clock ≤ source.clock := by
  exact Nat.le_of_eq (StackPropsAllocationConstants.allocConst word source target result execution).2.1
/-- The original store helper result is independently polymorphic. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "store_const_sem_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem storeConstSemClock {width resultWidth : Nat} [NeZero width] [NeZero resultWidth]
    {C F : Type} (first second : Nat) (source target : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult resultWidth))
    (execution : storeConstSem first second source = (result,target)) : target.clock ≤ source.clock := by
  exact Nat.le_of_eq (StackPropsAllocationConstants.storeConstSemConst first second source target result execution).2.1
/-- Full original instruction clock inequality over the native total primitive. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instClock {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width) (source target : StackSemStateFiniteExact width C F)
    (execution : instHOL instruction source = some target) : target.clock ≤ source.clock := by
  exact Nat.le_of_eq (StackPropsInstructionConstants.instConst instruction source target execution).2.1
/-- Full original shared-memory dispatch clock inequality, all result branches. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_op_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem shMemOpClock {width : Nat} [NeZero width] {C F : Type}
    (operation : WordMemOp) (register : Nat) (address : BitVec width)
    (source target : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : shMemOp operation register address source = (result,target)) : target.clock ≤ source.clock := by
  exact Nat.le_of_eq (StackPropsSharedMemoryClock.shMemOpConst operation register address source target result execution).1
end Flapjack.StackSemClock
