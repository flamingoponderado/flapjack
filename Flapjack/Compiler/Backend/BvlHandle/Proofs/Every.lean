module

public import Flapjack.Compiler.Backend.Semantics.BvlProps.Every

@[expose] public section

/-! Source list lemmas for the recursive BVL expression predicate. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlProps

/-- The recursive property holds exactly for each list member. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bEvery_MEM"]
theorem bEvery_mem (p : Bvl.Exp → Prop) (xs : List Bvl.Exp) :
    bEvery p xs ↔ ∀ x ∈ xs, bEvery p [x] := by
  rw [bEvery_every, List.forall_iff_forall_mem]

/-- A singleton and a tail satisfying the recursive property form a list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bEvery_CONS"]
theorem bEvery_cons (p : Bvl.Exp → Prop) (x : Bvl.Exp) (xs : List Bvl.Exp)
    (premises : bEvery p [x] ∧ bEvery p xs) : bEvery p (x :: xs) := by
  apply (bEvery_mem p (x :: xs)).2
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · exact premises.1
  · exact (bEvery_mem p xs).1 premises.2 e member

end Flapjack.Compiler.Backend.BvlHandle.Proofs
