import Flapjack.Misc.BalancedMap.Semantics
import Mathlib.Data.Set.Insert

namespace Flapjack.Test.BalancedMapSemantics
open Misc.BalancedMap

private def cmp (x y : Nat) : Ordering :=
  if x = y then .eq else if x < y then .lt else .gt
private def malformed : Map Nat Nat :=
  .bin 0 10 100 (.bin 90 20 200 .tip .tip) (.bin 80 20 300 .tip .tip)

private theorem keySet_cmp (key : Nat) : keySet cmp key = {key} := by
  ext query
  by_cases h : key = query
  · simp [keySet, cmp, h]
  · by_cases hlt : key < query <;> simp [keySet, cmp, h, hlt, eq_comm]

-- Original complete observations: root update, left-biased collision, absence,
-- and two arbitrary comparators whose equivalence-class keys all coincide.
example : (toFmap cmp malformed).lookup (keySet cmp 10) = some 100 := by
  rw [holFmapAsFiniteSupportResultWitness_toFmap]
  simp [malformed, semanticLookup, keySet_cmp]
example : (toFmap cmp malformed).lookup (keySet cmp 20) = some 200 := by
  rw [holFmapAsFiniteSupportResultWitness_toFmap]
  simp [malformed, semanticLookup, keySet_cmp, Set.singleton_eq_singleton_iff]
example : (toFmap cmp malformed).lookup (keySet cmp 30) = none := by
  rw [holFmapAsFiniteSupportResultWitness_toFmap]
  simp [malformed, semanticLookup, keySet_cmp, Set.singleton_eq_singleton_iff]
example : (toFmap (fun (_ _ : Nat) => .eq) malformed).lookup Set.univ = some 100 := by
  rw [holFmapAsFiniteSupportResultWitness_toFmap]
  simp [malformed, semanticLookup, keySet]
example : (toFmap (fun (_ _ : Nat) => .lt) malformed).lookup ∅ = some 100 := by
  rw [holFmapAsFiniteSupportResultWitness_toFmap]
  simp [malformed, semanticLookup, keySet]
example : (toFmap cmp (.tip : Map Nat Nat)).lookup (keySet cmp 10) = none := rfl

end Flapjack.Test.BalancedMapSemantics

def Flapjack.Test.BalancedMapSemantics.runChecks : IO Bool := do
  IO.println "BalancedMapSemantics: 6 original HOL set-key kernel fixtures checked"
  return true
