module

public import Flapjack.HOL.Unification.Walkstar.Relation
public import Flapjack.Misc.Bag.MultisetOrder.WellFounded
import Mathlib.Order.RelClasses

@[expose] public section

/-! Well-foundedness of HOL's first-order walkstar ordering. -/
namespace Flapjack.HOL.Unification

/-- The canonical substitution survives the finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarThWF_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_thWF"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarThWF {α : Type} (s : HolFiniteMapExact Nat (Term α)) (hw : wfs s) :
    WellFounded (walkstarR s : Term α → Term α → Prop) := by
  have bags := (wfBagMultisetStep (Relation.TransGen (vR s)) hw.transGen).transGen
  have terms : WellFounded (fun a b : Term α => pairCount a < pairCount b) :=
    measure pairCount |>.wf
  apply Subrelation.wf _ (InvImage.wf (fun t : Term α => (varb t, t)) (bags.prod_lex terms))
  intro a b h
  rcases h with h | ⟨eq, lt⟩
  · exact Prod.Lex.left _ _ h
  · change Prod.Lex (Relation.TransGen (bagMultisetStep (Relation.TransGen (vR s))))
      (fun a b : Term α => pairCount a < pairCount b) (varb a, a) (varb b, b)
    rw [eq]
    exact Prod.Lex.right _ lt

end Flapjack.HOL.Unification
