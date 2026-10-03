import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Full separation-based memory read and native load preservation from
stack_removeProofScript.sml. The generic frame law retains independent address
and payload types; memory heaps/domains need not be finite or canonical maps. -/
namespace Flapjack.Compiler.Backend.StackRemove.MemoryReads
open Flapjack

/-- Full original generic frame read: an address in the source graph domain
belongs to the target graph domain and has exactly the same value there. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_fun2set_IMP_read"]
theorem memoryFun2SetImpRead {α β : Type} (memory targetMemory : α → β)
    (domain targetDomain : α → Prop) (frame : ((α × β) → Prop) → Prop) (address : α)
    (hypothesis : SetSep.star (memoryHOL memory domain) frame
      (SetSep.fun2Set (targetMemory, targetDomain)) ∧ domain address) :
    targetDomain address ∧ targetMemory address = memory address := by
  rcases hypothesis with ⟨⟨left, right, partition, leftMemory, _frame⟩, inDomain⟩
  have inLeft : left (address, memory address) := by
    rw [leftMemory]
    exact (SetSep.fun2SetThm memory domain address (memory address)).mpr ⟨rfl, inDomain⟩
  have inTarget : SetSep.fun2Set (targetMemory, targetDomain) (address, memory address) := by
    rw [← partition.1]
    exact Or.inl inLeft
  have member := (SetSep.fun2SetThm targetMemory targetDomain address (memory address)).mp inTarget
  exact ⟨member.2, member.1⟩

/-- Flapjack-specific canonical codec witness for the actual imported evaluator
state; no separate HOL declaration is claimed for this representation lemma. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-domain membership yields target membership and exact read equality
through all five original separated heap assertions in the full state relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_read"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelRead {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧ source.mdomain address = true) :
    target.mdomain address = true ∧ target.memory address = source.memory address := by
  rcases hypothesis with ⟨relation, inDomain⟩
  have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dsimp only at heaps
  cases baseLookup : target.regs.lookup (pointer + 1) with
  | none =>
    simp only [baseLookup] at heaps
    exact heaps.2.elim
  | some value =>
    cases value with
    | loc block offset =>
      simp only [baseLookup] at heaps
      exact heaps.2.elim
    | word base =>
      simp only [baseLookup] at heaps
      rcases heaps.2.2.2.2 with ⟨heap4, heapStack, split4, assertion4, _stack⟩
      rcases assertion4 with ⟨heap3, heapStore, split3, assertion3, _store⟩
      rcases assertion3 with ⟨heap2, heapSpace, split2, assertion2, _space⟩
      rcases assertion2 with ⟨heap1, heapBitmaps, split1, assertion1, _bitmaps⟩
      have inMemory : heap1 (address, source.memory address) := by
        rw [assertion1]
        exact (SetSep.fun2SetThm source.memory (fun a => source.mdomain a = true)
          address (source.memory address)).mpr ⟨rfl, inDomain⟩
      have inHeap2 : heap2 (address, source.memory address) := by
        rw [← split1.1]; exact Or.inl inMemory
      have inHeap3 : heap3 (address, source.memory address) := by
        rw [← split2.1]; exact Or.inl inHeap2
      have inHeap4 : heap4 (address, source.memory address) := by
        rw [← split3.1]; exact Or.inl inHeap3
      have inTarget : SetSep.fun2Set (target.memory, fun a => target.mdomain a = true)
          (address, source.memory address) := by
        rw [← split4.1]; exact Or.inl inHeap4
      have member := (SetSep.fun2SetThm target.memory (fun a => target.mdomain a = true)
        address (source.memory address)).mp inTarget
      exact ⟨member.2, member.1⟩

/-- Exact native domain-checked load simulation: successful source load yields
that same value in the target, without a supplied target lookup or read fact. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_load_imp"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemLoadImp {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (value : WordLocW width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackSemStateOps.memLoad address source = some value) :
    StackSemStateOps.memLoad address target = some value := by
  rcases hypothesis with ⟨relation, sourceLoad⟩
  unfold StackSemStateOps.memLoad at sourceLoad
  cases domainEq : source.mdomain address with
  | false => simp [domainEq] at sourceLoad
  | true =>
    have sourceValue : source.memory address = value := by
      simpa only [domainEq, Bool.true_eq, ite_true, Option.some.injEq] using sourceLoad
    have targetRead := stateRelRead jump bounds pointer source target address ⟨relation, domainEq⟩
    simp only [StackSemStateOps.memLoad, targetRead.1, ite_true]
    exact congrArg some (targetRead.2.trans sourceValue)

end Flapjack.Compiler.Backend.StackRemove.MemoryReads
