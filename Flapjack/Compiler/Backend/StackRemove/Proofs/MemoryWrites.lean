import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryReads

namespace Flapjack.Compiler.Backend.StackRemove.MemoryWrites
open Flapjack

open Classical in
/-- Full generic memory update frame law. Disjointness and the functional graph
force the frame to contain no pair at the updated address; no frame-preservation
premise or finite-domain restriction is imposed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_write"]
theorem memoryWrite {α β : Type} (memory targetMemory : α → β)
    (domain targetDomain : α → Prop) (frame : ((α × β) → Prop) → Prop)
    (address : α) (value : β)
    (hypothesis : domain address ∧ targetDomain address ∧
      SetSep.star (memoryHOL memory domain) frame
        (SetSep.fun2Set (targetMemory, targetDomain))) :
    SetSep.star
      (memoryHOL (fun key => if key = address then value else memory key) domain) frame
      (SetSep.fun2Set ((fun key => if key = address then value else targetMemory key),
        targetDomain)) := by
  rcases hypothesis with ⟨inDomain, inTargetDomain, left, right, partition, leftMemory, frameRight⟩
  have oldRead := MemoryReads.memoryFun2SetImpRead memory targetMemory domain targetDomain
    frame address ⟨⟨left, right, partition, leftMemory, frameRight⟩, inDomain⟩
  have noFrame : ∀ payload, ¬ right (address, payload) := by
    intro payload member
    have graph : SetSep.fun2Set (targetMemory, targetDomain) (address, payload) := by
      rw [← partition.1]
      exact Or.inr member
    have read := (SetSep.fun2SetThm targetMemory targetDomain address payload).mp graph
    have leftMember : left (address, payload) := by
      rw [leftMemory]
      exact (SetSep.fun2SetThm memory domain address payload).mpr
        ⟨oldRead.2.symm.trans read.1, inDomain⟩
    exact partition.2 (address, payload) ⟨leftMember, member⟩
  let updatedLeft := SetSep.fun2Set
    ((fun key => if key = address then value else memory key), domain)
  refine ⟨updatedLeft, right, ⟨?_, ?_⟩, rfl, frameRight⟩
  · funext entry
    rcases entry with ⟨key, payload⟩
    apply propext
    by_cases same : key = address
    · subst key
      simp only [updatedLeft, SetSep.fun2SetThm, ite_true, inDomain, inTargetDomain,
        and_true, noFrame payload, or_false]
    · have oldPartition := congrFun partition.1 (key, payload)
      rw [leftMemory] at oldPartition
      simpa only [updatedLeft, SetSep.fun2SetThm, same, ite_false] using
        (show (SetSep.fun2Set (memory, domain) (key, payload) ∨ right (key, payload)) ↔
          SetSep.fun2Set (targetMemory, targetDomain) (key, payload) from
          iff_of_eq oldPartition)
  · rintro ⟨key, payload⟩ ⟨memberLeft, memberRight⟩
    by_cases same : key = address
    · subst key
      exact noFrame payload memberRight
    · have oldLeft : left (key, payload) := by
        rw [leftMemory]
        simpa only [updatedLeft, SetSep.fun2SetThm, same, ite_false] using memberLeft
      exact partition.2 (key, payload) ⟨oldLeft, memberRight⟩

end Flapjack.Compiler.Backend.StackRemove.MemoryWrites
