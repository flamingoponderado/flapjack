import Flapjack.Compiler.Backend.StackRemove.Proofs.Memory
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack

/-- Full original separated function-graph domain inclusion. Arbitrary
independent address/value types, arbitrary frame and infinite domains remain;
no word, finite-support or evaluator premise is added. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_fun2set_SUBSET"]
theorem memoryFun2SetSubset {α β : Type} (memory targetMemory : α → β)
    (domain targetDomain : α → Prop) (frame : ((α × β) → Prop) → Prop)
    (hypothesis : SetSep.star (memoryHOL memory domain) frame
      (SetSep.fun2Set (targetMemory, targetDomain))) :
    ∀ address, domain address → targetDomain address := by
  rcases hypothesis with ⟨left, right, partition, leftMemory, _⟩
  change left = SetSep.fun2Set (memory, domain) at leftMemory
  subst left
  intro address inDomain
  have inSource : SetSep.fun2Set (memory, domain) (address, memory address) :=
    (SetSep.fun2SetThm memory domain address (memory address)).mpr ⟨rfl, inDomain⟩
  have inTarget : SetSep.fun2Set (targetMemory, targetDomain) (address, memory address) := by
    rw [← partition.1]
    exact Or.inl inSource
  exact ((SetSep.fun2SetThm targetMemory targetDomain address (memory address)).mp inTarget).2

end Flapjack.Compiler.Backend.StackRemove
