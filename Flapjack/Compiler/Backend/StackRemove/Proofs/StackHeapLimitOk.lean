import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.StackRemove

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeapLimitOk
open Flapjack

/-- Genuine canonical roundtrip for the imported actual state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Complete original heap/stack limit predicate. The pair argument, actual
HeapLength store word, natural byte-capacity bound and stack-length equality
are retained. Word construction/multiplication is modular; the capacity
comparison uses the original natural product and dimword. No dimension,
register, heap-separation or successful-initializer premise is added. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_heap_limit_ok_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def stackHeapLimitOk {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (limits : Nat × Nat) : Prop :=
  source.store.lookup .heapLength =
    some (.word (BitVec.ofNat width limits.2 * bytesInWord width)) ∧
  limits.2 * (width / 8) < 2 ^ width ∧
  limits.1 = source.stack.length

end Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeapLimitOk
