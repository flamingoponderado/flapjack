import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals

namespace Flapjack.Compiler.Backend.WordAlloc

/-- The full native bound-monotonicity result. Both locals trees retain HOL's
generic payload; the sole premise is the original relation and bound ordering.
The accepted guarded selector correspondence is inherited from `ssaLocalsRel`. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_more"]
theorem ssaLocalsRelMore {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (nextOut : Nat) :
    ssaLocalsRel next ssa source target ∧ next ≤ nextOut →
      ssaLocalsRel nextOut ssa source target := by
  rintro ⟨⟨mapped, matching⟩, bound⟩
  refine ⟨mapped, ?_⟩
  intro key value found
  rcases matching key value found with ⟨domain, lookup, allocated⟩
  exact ⟨domain, lookup, fun isAllocated =>
    Nat.lt_of_lt_of_le (allocated isAllocated) bound⟩

end Flapjack.Compiler.Backend.WordAlloc
