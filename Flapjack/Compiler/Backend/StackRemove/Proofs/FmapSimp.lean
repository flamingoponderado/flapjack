import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-! Finite-map update reordering of `stack_removeProofScript.sml` (3041-3046),
used for the initializer's register updates. HOL `|+` on `num` keys is
`HolFiniteMapExact.updateEq`, with HOL key equality as `DecidableEq`.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.FmapSimp
open Flapjack

/-- Complete original equality for an arbitrary map and arbitrary values:
the overwritten first update of key `0` disappears and the final updates
commute. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "fmap_simp_lemma1"
  (fmap_as_finite_support_equality)]
theorem fmapSimpLemma1 {β : Type} (g : HolFiniteMapExact Nat β) (x y z : β) :
    ((g.updateEq (0, x)).updateEq (5, y)).updateEq (0, z) =
      (g.updateEq (0, z)).updateEq (5, y) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  by_cases h0 : key = 0 <;> by_cases h5 : key = 5 <;> simp_all

/-- Unconditional lookup-level witness for `fmapSimpLemma1`: both sides agree
at the same universally bound key. -/
theorem holFmapAsFiniteSupportEqualityWitness_fmapSimpLemma1 {β : Type}
    (g : HolFiniteMapExact Nat β) (x y z : β) (key : Nat) :
    (((g.updateEq (0, x)).updateEq (5, y)).updateEq (0, z)).lookup key =
      ((g.updateEq (0, z)).updateEq (5, y)).lookup key := by
  simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  by_cases h0 : key = 0 <;> by_cases h5 : key = 5 <;> simp_all

end Flapjack.Compiler.Backend.StackRemove.Proofs.FmapSimp
