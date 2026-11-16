module

public import Flapjack.HOL.Unification.Term.VarBag
public import Flapjack.HOL.Unification.Subst
public import Flapjack.Misc.Bag.MultisetOrder

@[expose] public section

/-! HOL's lexicographic termination relation for first-order normalization. -/
namespace Flapjack.HOL.Unification

/-- The canonical substitution survives the finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarR_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstarR_def"
  (fmap_as_finite_support_parameters := [s])]
def walkstarR {α β : Type} (s : HolFiniteMapExact Nat (Term β)) (t1 t2 : Term α) : Prop :=
  Relation.TransGen (bagMultisetStep (Relation.TransGen (vR s))) (varb t1) (varb t2) ∨
    (varb t1 = varb t2 ∧ pairCount t1 < pairCount t2)

end Flapjack.HOL.Unification
