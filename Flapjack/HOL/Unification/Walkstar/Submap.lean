module

public import Flapjack.HOL.Unification.Walkstar.Induction
public import Flapjack.HOL.Unification.Walk.Submap

@[expose] public section

namespace Flapjack.HOL.Unification

/-- The smaller substitution survives the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- The larger substitution survives the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_SUBMAP"
  (fmap_as_finite_support_parameters := [s, sx])]
theorem walkstarSubmap {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (sx : HolFiniteMapExact Nat (Term α)) (t : Term α)
    (h : s.submap sx ∧ wfs sx) : walkstar sx t = walkstar sx (walkstar s t) := by
  have hs : wfs s := wfsSubmap sx s ⟨h.2, h.1⟩
  have all : ∀ t, walkstar sx t = walkstar sx (walkstar s t) := by
    apply walkstarInd s hs
    intro t ih
    have heq := walkstarEq s hs t
    have hbig := walkstarEq sx h.2 t
    cases t with
    | const c =>
      simp only [walk] at heq hbig
      rw [heq, hbig]
    | pair a b =>
      have ha := ih.2 a b rfl
      have hb := ih.1 a b rfl
      simp only [walk] at heq hbig
      rw [heq, hbig, walkstarEq sx h.2 (.pair (walkstar s a) (walkstar s b))]
      simp only [walk]
      rw [← ha, ← hb]
    | var v =>
      simp only [walk] at heq hbig
      have subWalk := vwalkSubmap sx h.2 v s h.1
      cases small : vwalk s v with
      | var u =>
        simp only [small] at subWalk heq
        rw [heq, hbig, walkstarEq sx h.2 (.var u)]
        simp only [walk]
        rw [subWalk]
      | const c =>
        simp only [small] at subWalk heq
        rw [heq, hbig, walkstarEq sx h.2 (.const c)]
        simp only [walk, subWalk]
      | pair a b =>
        have ha := ih.2 a b (by simpa [walk] using small)
        have hb := ih.1 a b (by simpa [walk] using small)
        simp only [small] at subWalk heq
        rw [heq, hbig, walkstarEq sx h.2 (.pair (walkstar s a) (walkstar s b))]
        simp only [walk, subWalk]
        rw [← ha, ← hb]
  exact all t

end Flapjack.HOL.Unification
