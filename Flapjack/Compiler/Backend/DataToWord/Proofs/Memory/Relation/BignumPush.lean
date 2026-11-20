module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A bignum cell already present in the heap can be added to the abstract
stack. This Flapjack helper supplies the final stack step of HOL's
`bignum_alt_thm`. -/
theorem bcStackRefInv_pushBignum {width : Nat} [NeZero width] (conf : Config) (next : Nat)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (ptr : Nat) (i : Int) (large : ¬ smallInt width i)
    (found : heapLookup ptr heap = some (bignumRep i))
    (inv : bcStackRefInv conf next stack refs (roots, heap, be)) :
    bcStackRefInv conf next (.number i :: stack) refs (.pointer ptr (.word 0) :: roots, heap, be) := by
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, values, cells⟩ := inv
  refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
  · intro stamp domain
    obtain ⟨value, member, timestamp⟩ := tfTimestamps stamp domain
    refine ⟨value, ?_, timestamp⟩
    rcases member with inRef | inStack
    · exact Or.inl inRef
    · exact Or.inr (List.mem_cons_of_mem _ inStack)
  · simpa using blocksUnique_number [] stack refs next i unique
  · apply List.Forall₂.cons
    · exact (valueInv_number conf i refs _ f tf heap).mpr (by simp [large, found])
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
