module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A Word64 cell already present in the heap can be added to the abstract
stack. This Flapjack helper supplies the final stack step of HOL's
`word64_alt_thm`. -/
theorem bcStackRefInv_pushWord64 {width : Nat} [NeZero width] (conf : Config) (next : Nat)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (ptr : Nat) (word : BitVec 64)
    (found : heapLookup ptr heap = some (word64Rep word))
    (inv : bcStackRefInv conf next stack refs (roots, heap, be)) :
    bcStackRefInv conf next (.word64 word :: stack) refs (.pointer ptr (.word 0) :: roots, heap, be) := by
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, values, cells⟩ := inv
  refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
  · intro stamp domain
    obtain ⟨value, member, timestamp⟩ := tfTimestamps stamp domain
    refine ⟨value, ?_, timestamp⟩
    rcases member with inRef | inStack
    · exact Or.inl inRef
    · exact Or.inr (List.mem_cons_of_mem _ inStack)
  · simpa using blocksUnique_word64 [] stack refs next word unique
  · apply List.Forall₂.cons
    · exact (valueInv_word64 conf word refs _ f tf heap).mpr ⟨ptr, rfl, found⟩
    · exact values
  · intro n ⟨reachable, domain⟩
    apply cells n
    refine ⟨?_, domain⟩
    obtain ⟨value, start, member, ref, path⟩ := reachable
    rcases List.mem_cons.mp member with same | inStack
    · subst value
      simp [getRefs] at ref
    · exact ⟨value, start, inStack, ref, path⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
