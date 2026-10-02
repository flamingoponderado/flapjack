import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryLoads
namespace Flapjack.Compiler.Backend.StackRemove.BytearrayReads
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

/-- Full original bytearray read preservation: arbitrary source count/address,
actual source read success and the complete state relation. Word-address
increment wraps exactly as in HOL; no length, alignment or no-wrap bound is
added, and successful target reading is the proved conclusion. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "read_bytearray_IMP_read_bytearray"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem readBytearrayImp {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (address : BitVec width) (source target : StackSemStateFiniteExact width C F)
    (bytes : List (BitVec 8))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      readBytearrayWordHOL address count
        (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes) :
    readBytearrayWordHOL address count
      (memLoadByteAuxExact target.memory target.mdomain target.be) = some bytes := by
  rcases hypothesis with ⟨relation, run⟩
  induction count generalizing address bytes with
  | zero => simpa only [readBytearrayWordHOL] using run
  | succ count ih =>
    simp only [readBytearrayWordHOL] at run ⊢
    cases head : memLoadByteAuxExact source.memory source.mdomain source.be address with
    | none => simp [head] at run
    | some byte =>
      have targetHead := MemoryLoads.memLoadByteAuxImp jump bounds pointer source target address byte ⟨relation, head⟩
      rw [head] at run
      rw [targetHead]
      cases tail : readBytearrayWordHOL (address + 1) count
          (memLoadByteAuxExact source.memory source.mdomain source.be) with
      | none =>
        rw [tail] at run
        simp at run
      | some rest =>
        have targetTail := ih (address + 1) rest tail
        rw [tail] at run
        rw [targetTail]
        exact run
end Flapjack.Compiler.Backend.StackRemove.BytearrayReads
