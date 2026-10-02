import Flapjack.Compiler.Backend.RegAlloc.ProductionPrefreeze

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- The input cost-tree relation preserves absent keys as well as present
costs. This is actual/native carrier infrastructure, not a HOL declaration. -/
def ProductionCostRel (native : Spt Nat) (production : CakeNodeMap Nat) : Prop :=
  ∀ key, production.get key = sptLookup key native

private theorem costLookup_first (key : Nat) (entries : NatInfoMap Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    simp only [lookupNatInfo, sptAListLookup, Bool.beq_eq_decide_eq]
    by_cases equal : key = other
    · subst other
      simp
    · simp [equal, Ne.symm equal, ih]

/-- The executed spill-cost embedding represents the native tree built from
the same associations, unconditionally. First bindings win at duplicate keys;
keys outside the dense allocation remain observable. This constructs the
input relation used by the selector proof, with no target lookup premise. -/
theorem cakeSpillCostMap_production (dimension : Nat) (entries : NatInfoMap Nat) :
    ProductionCostRel (sptFromAList entries) (cakeSpillCostMap dimension entries) := by
  intro key
  rw [cakeSpillCostMap, CakeNodeMap.get_ofNatInfoMap, sptLookup_sptFromAList]
  exact costLookup_first key entries

/-- Actual maximum-degree selection preserves the native result pair and
unchanged state, including skipped candidates, ties, and replaced candidates.
The degree domain comes from the original state invariant. This is untagged
actual/native infrastructure rather than another HOL selector port. -/
theorem stExListMaxDeg_production (items : List Nat) (selected value : Nat)
    (acc : List Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    stExListMaxDeg items native.dim selected value acc native =
      (.success (cakeStExListMaxDeg production.degrees items native.dim selected value acc), native) := by
  induction items generalizing selected value acc with
  | nil => simp [stExListMaxDeg, cakeStExListMaxDeg, ret]
  | cons node rest ih =>
    by_cases bound : node < native.dim
    · have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
      have read := related.degree_read node degreeBound
      simp only [stExListMaxDeg, cakeStExListMaxDeg, bound, if_true,
        degreesSubEqn, degreeBound, holEl_eq_getElem node native.degrees degreeBound,
        read, Option.getD_some, Translator.Monadic.MonadBase.bind]
      split <;> exact ih _ _ _
    · simp only [stExListMaxDeg, cakeStExListMaxDeg, bound, if_false]
      exact ih _ _ _

/-- Actual minimum-cost selection preserves the native result pair and
unchanged state from an input cost-map relation. No selected output or target
evaluation is assumed. This is actual/native infrastructure without a HOL tag. -/
theorem stExListMinCost_production (costs : Spt Nat) (actualCosts : CakeNodeMap Nat)
    (costRel : ProductionCostRel costs actualCosts)
    (items : List Nat) (selected value : Nat) (acc : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    stExListMinCost costs items native.dim selected value acc native =
      (.success (cakeStExListMinCost production.degrees actualCosts items native.dim selected value acc), native) := by
  induction items generalizing selected value acc with
  | nil => simp [stExListMinCost, cakeStExListMinCost, ret]
  | cons node rest ih =>
    by_cases bound : node < native.dim
    · have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
      have read := related.degree_read node degreeBound
      have costRead : (actualCosts.get node).getD 0 = lookupAny node costs 0 := by
        rw [costRel node]
        cases readCost : sptLookup node costs <;> simp [lookupAny, readCost]
      simp only [stExListMinCost, cakeStExListMinCost, bound, if_true,
        degreesSubEqn, degreeBound, holEl_eq_getElem node native.degrees degreeBound,
        read, Option.getD_some, cakeSafeDiv, costRead,
        Translator.Monadic.MonadBase.bind, ret]
      split <;> exact ih _ _ _
    · simp only [stExListMinCost, cakeStExListMinCost, bound, if_false]
      exact ih _ _ _

end Flapjack.RegAlloc
