module

public import Flapjack.HolRef
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "WF_FINITE_PSUBSET"]
theorem wfFinitePsubset {α : Type} :
    WellFounded (fun s1 s2 : Set α => s1 ⊂ s2 ∧ s2.Finite) := by
  apply Subrelation.wf _ (measure (fun s : Set α => s.ncard)).wf
  intro s1 s2 h
  exact Set.ncard_lt_ncard h.1 h.2

end Flapjack.HOL.Unification
