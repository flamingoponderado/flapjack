import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
namespace Flapjack.Compiler.Backend.StackRemove.StackPointer
open Flapjack.Compiler.Backend.StackRemove
open Flapjack
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- The full original relation supplies the existential stack base, both
reserved pointer lookups, both bounds and the complete separated heap. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelGetVarK {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ base : BitVec width,
      StackSemStateOps.getVar (pointer + 1) target = some (.word base) ∧
      width / 8 * maxStackAlloc ≤ base.toNat ∧
      base.toNat + (bytesInWord width).toNat * source.stack.length < 2 ^ width ∧
      StackSemStateOps.getVar pointer target = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) ∧
      SetSep.star
        (SetSep.star
          (SetSep.star
            (SetSep.star (memoryHOL source.memory (fun address => source.mdomain address = true))
              (Misc.wordList (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
                ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)))
            (Misc.wordListExists ((theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width) +
              bytesInWord width * BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length)
              source.dataBuffer.spaceLeft))
          (wordStoreHOL base source.store))
        (Misc.wordList base source.stack)
        (SetSep.fun2Set (target.memory, fun address => target.mdomain address = true)) := by
  have heap := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dsimp only at heap
  cases lookup : target.regs.lookup (pointer + 1) with
  | none => simp [lookup] at heap
  | some value =>
    cases value with
    | loc first second => simp [lookup] at heap
    | word base =>
      simp only [lookup] at heap
      exact ⟨base, lookup, heap.2⟩
end Flapjack.Compiler.Backend.StackRemove.StackPointer
