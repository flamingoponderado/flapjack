import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryReads
import Flapjack.Compiler.Backend.Semantics.WordSem

namespace Flapjack.Compiler.Backend.StackRemove.MemoryLoads
open Flapjack

/-- Flapjack-specific canonical codec witness for the actual imported state;
no separate HOL declaration is claimed for this representation lemma. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original successful-load implication. The aligned target domain and
old word are derived from the full separated relation, retaining endianness. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_32_IMP"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memLoad32Imp {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (value : BitVec 32)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      memLoad32Exact source.memory source.mdomain source.be address = some value) :
    memLoad32Exact target.memory target.mdomain target.be address = some value := by
  rcases hypothesis with ⟨relation, run⟩
  cases aligned : riscvAlignedHOL 2 address with
  | false => simp [memLoad32Exact, aligned] at run
  | true =>
      cases old : source.memory (riscvByteAlignHOL address) with
      | loc block offset => simp [memLoad32Exact, aligned, old] at run
      | word oldWord =>
        cases inSource : source.mdomain (riscvByteAlignHOL address) with
        | false => simp [memLoad32Exact, aligned, old, inSource] at run
        | true =>
          have read := MemoryReads.stateRelRead jump bounds pointer source target
            (riscvByteAlignHOL address) ⟨relation, inSource⟩
          have targetOld : target.memory (riscvByteAlignHOL address) = .word oldWord :=
            read.2.trans old
          have endian := relation.2.2.2.2.2.2.1
          simpa only [memLoad32Exact, aligned, targetOld, old, inSource, read.1, endian, ite_true] using run

/-- Full original successful-load implication. The aligned target domain and
old word are derived from the full separated relation, retaining endianness. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_byte_aux_IMP"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memLoadByteAuxImp {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (address : BitVec width)
    (value : BitVec 8)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      memLoadByteAuxExact source.memory source.mdomain source.be address = some value) :
    memLoadByteAuxExact target.memory target.mdomain target.be address = some value := by
  rcases hypothesis with ⟨relation, run⟩
  cases old : source.memory (riscvByteAlignHOL address) with
  | loc block offset => simp [memLoadByteAuxExact, old] at run
  | word oldWord =>
    cases inSource : source.mdomain (riscvByteAlignHOL address) with
    | false => simp [memLoadByteAuxExact, old, inSource] at run
    | true =>
      have read := MemoryReads.stateRelRead jump bounds pointer source target
        (riscvByteAlignHOL address) ⟨relation, inSource⟩
      have targetOld : target.memory (riscvByteAlignHOL address) = .word oldWord :=
        read.2.trans old
      have endian := relation.2.2.2.2.2.2.1
      simpa only [memLoadByteAuxExact, targetOld, old, inSource, read.1, endian, ite_true] using run

end Flapjack.Compiler.Backend.StackRemove.MemoryLoads
