module

public import Flapjack.HOL.Unification.Walkstar.Relation
public import Flapjack.HOL.Unification.Walkstar
public import Flapjack.HOL.Unification.Walk.Dependency
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The two recursive calls of the original walkstar definition decrease. -/
namespace Flapjack.HOL.Unification

private theorem variableChildDecrease {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (hw : wfs s) (n : Nat) (a b child : Term α)
    (hwalk : vwalk s n = .pair a b)
    (hchild : ∀ u, vars child u → vars (.pair a b) u) :
    walkstarR s child (.var n) := by
  left
  apply Relation.TransGen.single
  refine ⟨finiteVarb child, finiteVarb (.var n), n, varb child, emptyBag, ?_, ?_, ?_⟩
  · exact (bagUnion_empty_right _).symm
  · simpa only [varb] using (bagUnion_empty_left (bagInsert n emptyBag)).symm
  · intro u hu
    apply vwalkVR s hw n u
    constructor
    · rw [hwalk]
      exact hchild u ((inVarbVars u child).mp hu)
    · rw [hwalk]
      simp

private theorem pairChildrenDecrease {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (a b : Term α) : walkstarR s a (.pair a b) ∧ walkstarR s b (.pair a b) := by
  classical
  constructor
  · by_cases hb : varb b = emptyBag
    · right
      refine ⟨?_, ?_⟩
      · simp only [varb, hb, bagUnion_empty_right]
      · simp [pairCount]; omega
    · left
      simpa only [varb] using
        (tcMlt1Union2I (Relation.TransGen (vR s)) (varb b) (varb a)
          ⟨finiteVarb b, finiteVarb a, hb⟩)
  · by_cases ha : varb a = emptyBag
    · right
      refine ⟨?_, ?_⟩
      · simp only [varb, ha, bagUnion_empty_left]
      · simp [pairCount]; omega
    · left
      simpa only [varb] using
        (tcMlt1Union1I (Relation.TransGen (vR s)) (varb b) (varb a)
          ⟨finiteVarb b, finiteVarb a, ha⟩)

private theorem walkstarChildren {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (hw : wfs s) (t a b : Term α) (h : walk s t = .pair a b) :
    walkstarR s a t ∧ walkstarR s b t := by
  cases t with
  | var n =>
    have hwalk : vwalk s n = .pair a b := by simpa [walk] using h
    exact ⟨variableChildDecrease s hw n a b a hwalk (fun _ hu => Or.inl hu),
      variableChildDecrease s hw n a b b hwalk (fun _ hu => Or.inr hu)⟩
  | pair x y =>
    simp only [walk, Term.pair.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact pairChildrenDecrease s x y
  | const c => simp [walk] at h

/-- The substitution uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarTh1_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_th1"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarTh1 {α : Type} (s : HolFiniteMapExact Nat (Term α)) (hw : wfs s) :
    ∀ t a b, walk s t = .pair a b → walkstarR s a t := by
  intro t a b h
  exact (walkstarChildren s hw t a b h).1

/-- The second recursive call uses the same canonical substitution codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarTh2_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_th2"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarTh2 {α : Type} (s : HolFiniteMapExact Nat (Term α)) (hw : wfs s) :
    ∀ t a b, walk s t = .pair a b → walkstarR s b t := by
  intro t a b h
  exact (walkstarChildren s hw t a b h).2

end Flapjack.HOL.Unification
