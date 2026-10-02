import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryWrites
import Flapjack.Compiler.Backend.Semantics.WordSem

namespace Flapjack.Compiler.Backend.StackRemove.MemoryStores
open Flapjack

/-- Flapjack-specific factoring of the common point-update argument in the
three HOL store laws. This is internal proof infrastructure, with no separate
HOL original; both domain facts are discharged by the native store proofs. -/
theorem stateRelMemoryUpdate {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (value : WordLocW width) (relation : stateRelHOL jump bounds pointer source target)
    (inSource : source.mdomain address = true) (inTarget : target.mdomain address = true) :
    stateRelHOL jump bounds pointer
      {source with memory := fun key => if key = address then value else source.memory key}
      {target with memory := fun key => if key = address then value else target.memory key} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, ?_⟩
  cases lookup : target.regs.lookup (pointer + 1) with
  | none => simp only [lookup] at h25; exact h25.2.elim
  | some entry =>
    cases entry with
    | loc block offset => simp only [lookup] at h25; exact h25.2.elim
    | word base =>
      simp only [lookup] at h25 ⊢
      rcases h25 with ⟨position, lower, upper, register, heap⟩
      refine ⟨position, lower, upper, register, ?_⟩
      simp only [← SetSep.starAssoc] at heap ⊢
      have updateEq (oldMemory : BitVec width → WordLocW width) :
          (fun key => if key = address then value else oldMemory key) =
          (fun key => @ite (WordLocW width) (key = address)
            (Classical.propDecidable _) value (oldMemory key)) := by
        funext key
        by_cases same : key = address <;> simp only [same, ite_true, ite_false]
      rw [updateEq source.memory, updateEq target.memory]
      exact MemoryWrites.memoryWrite source.memory target.memory
        (fun key => source.mdomain key = true) (fun key => target.mdomain key = true)
        _ address value ⟨inSource, inTarget, heap⟩


/-- Canonical codec witness for the imported evaluator state; Flapjack proof
infrastructure without a separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Original scalar store helper: its original two successful native stores
preserve the full relation, including all five separated heap assertions. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_store"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemStore {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target postSource postTarget : StackSemStateFiniteExact width C F)
    (address : BitVec width) (value : WordLocW width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackSemStateOps.memStore address value source = some postSource ∧
      StackSemStateOps.memStore address value target = some postTarget) :
    stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, sourceStore, targetStore⟩
  cases inSource : source.mdomain address with
  | false => simp [StackSemStateOps.memStore, inSource] at sourceStore
  | true =>
    cases inTarget : target.mdomain address with
    | false => simp [StackSemStateOps.memStore, inTarget] at targetStore
    | true =>
      simp only [StackSemStateOps.memStore, inSource, ite_true, Option.some.injEq] at sourceStore
      simp only [StackSemStateOps.memStore, inTarget, ite_true, Option.some.injEq] at targetStore
      subst postSource
      subst postTarget
      exact stateRelMemoryUpdate jump bounds pointer source target address value relation
        inSource inTarget

/-- Complete original source-success store simulation. The target memory and
full updated state relation are derived, including endianness and old words. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_store_32"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemStore32 {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (value : BitVec 32) (resultMemory : BitVec width → WordLocW width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      memStore32Exact source.memory source.mdomain source.be address value = some resultMemory) :
    ∃ targetMemory, memStore32Exact target.memory target.mdomain target.be address value = some targetMemory ∧
      stateRelHOL jump bounds pointer {source with memory := resultMemory}
        {target with memory := targetMemory} := by
  rcases hypothesis with ⟨relation, run⟩
  cases aligned : riscvAlignedHOL 2 address with
  | false => simp [memStore32Exact, aligned] at run
  | true =>
      cases old : source.memory (riscvByteAlignHOL address) with
      | loc block offset => simp [memStore32Exact, aligned, old] at run
      | word oldWord =>
        cases inSource : source.mdomain (riscvByteAlignHOL address) with
        | false => simp [memStore32Exact, aligned, old, inSource] at run
        | true =>
          have read := MemoryReads.stateRelRead jump bounds pointer source target
            (riscvByteAlignHOL address) ⟨relation, inSource⟩
          have targetOld : target.memory (riscvByteAlignHOL address) = .word oldWord :=
            read.2.trans old
          have endian := relation.2.2.2.2.2.2.1
          simp only [memStore32Exact, aligned, old, inSource, ite_true, Option.some.injEq] at run
          subst resultMemory
          let v0 := setByteHOL8 address (getByteHOL8 (0 : BitVec 32) value source.be) oldWord source.be
          let v1 := setByteHOL8 (address + 1) (getByteHOL8 (1 : BitVec 32) value source.be) v0 source.be
          let v2 := setByteHOL8 (address + 2) (getByteHOL8 (2 : BitVec 32) value source.be) v1 source.be
          let v3 := setByteHOL8 (address + 3) (getByteHOL8 (3 : BitVec 32) value source.be) v2 source.be
          refine ⟨(fun key => if key = riscvByteAlignHOL address then .word v3 else target.memory key), ?_, ?_⟩
          · simp only [memStore32Exact, aligned, targetOld, read.1, endian, ite_true]
            rfl
          · exact stateRelMemoryUpdate jump bounds pointer source target
              (riscvByteAlignHOL address) _ relation inSource read.1

/-- Complete original source-success store simulation. The target memory and
full updated state relation are derived, including endianness and old words. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_store_byte_aux"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemStoreByteAux {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (value : BitVec 8) (resultMemory : BitVec width → WordLocW width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      memStoreByteAuxExact source.memory source.mdomain source.be address value = some resultMemory) :
    ∃ targetMemory, memStoreByteAuxExact target.memory target.mdomain target.be address value = some targetMemory ∧
      stateRelHOL jump bounds pointer {source with memory := resultMemory}
        {target with memory := targetMemory} := by
  rcases hypothesis with ⟨relation, run⟩
  cases old : source.memory (riscvByteAlignHOL address) with
  | loc block offset => simp [memStoreByteAuxExact, old] at run
  | word oldWord =>
    cases inSource : source.mdomain (riscvByteAlignHOL address) with
    | false => simp [memStoreByteAuxExact, old, inSource] at run
    | true =>
      have read := MemoryReads.stateRelRead jump bounds pointer source target
        (riscvByteAlignHOL address) ⟨relation, inSource⟩
      have targetOld : target.memory (riscvByteAlignHOL address) = .word oldWord :=
        read.2.trans old
      have endian := relation.2.2.2.2.2.2.1
      simp only [memStoreByteAuxExact, old, inSource, ite_true, Option.some.injEq] at run
      subst resultMemory
      refine ⟨(fun key => if key = riscvByteAlignHOL address then
        .word (setByteHOL8 address value oldWord source.be) else target.memory key), ?_, ?_⟩
      · simp only [memStoreByteAuxExact, targetOld, read.1, endian, ite_true]
      · exact stateRelMemoryUpdate jump bounds pointer source target
          (riscvByteAlignHOL address) _ relation inSource read.1

end Flapjack.Compiler.Backend.StackRemove.MemoryStores
