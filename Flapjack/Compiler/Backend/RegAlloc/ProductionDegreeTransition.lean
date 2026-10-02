import Flapjack.Compiler.Backend.RegAlloc.ProductionStateRelation
import Flapjack.Compiler.Backend.RegAlloc.Worklists
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Complete Unit transition result correspondence, including the retained
failure state. The production-only missing-slot error has no matching native
case and must be proved unreachable, rather than erased. Flapjack infrastructure. -/
def ProductionUnitResultRel (native : Exc Unit StateException × State)
    (production : CakeRaMResult) : Prop :=
  match native.1, production with
  | .success (), .success () state => ProductionStateRel native.2 state
  | .failure .Subscript, .failure .subscript state => ProductionStateRel native.2 state
  | _, _ => False

/-- Actual monadic degree decrement agrees with the already ported native
transition at every index, including Subscript and truncated zero decrement.
No valid-index or successful-result premise is added. This cross-implementation
relation has no independent HOL original and is deliberately untagged. -/
theorem decDeg_production_monadic (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    ProductionUnitResultRel (decDeg node native) (cakeDecDegMonadic node production) := by
  by_cases bound : node < native.degrees.length
  · have productionBound : node < production.degrees.slots.size := by
      rw [related.degrees.2.1]
      exact bound
    have slot : production.degrees.slots[node]? = some (some native.degrees[node]) := by
      have value := related.degree_read node bound
      have dense : production.degrees.slots[node] = some native.degrees[node] := by
        simpa [CakeNodeMap.get, productionBound] using value
      simpa [productionBound] using congrArg some dense
    have actual : cakeDecDegMonadic node production = .success ()
        {production with degrees := production.degrees.set node (native.degrees[node] - 1)} := by
      unfold cakeDecDegMonadic
      rw [if_pos productionBound, slot]
    have source : decDeg node native = (.success (),
        {native with degrees := native.degrees.set node (native.degrees[node] - 1)}) := by
      simp [decDeg, Translator.Monadic.MonadBase.bind, degreesSubEqn, updateDegreesEqn,
        bound, holEl_eq_getElem node native.degrees bound]
    simpa only [source, actual, ProductionUnitResultRel] using
      related.degree_write node (native.degrees[node] - 1) bound
  · have productionBound : ¬ node < production.degrees.slots.size := by
      rwa [related.degrees.2.1]
    have source : decDeg node native = (.failure .Subscript, native) := by
      simp [decDeg, Translator.Monadic.MonadBase.bind, degreesSubEqn, bound]
    simpa [source, ProductionUnitResultRel, cakeDecDegMonadic, productionBound] using related

/-- Pipeline latch correspondence keeps the native failure result explicit:
Subscript is stored in the production latch, while every original field still
represents the retained native state. It is not disguised as native success. -/
def ProductionLatchedUnitRel (native : Exc Unit StateException × State)
    (production : CakeRaState) : Prop :=
  match native.1 with
  | .success () => ProductionStateRel native.2 production
  | .failure .Subscript => production.failure = some .subscript ∧
      ProductionStateRel native.2 {production with failure := none}
  | .failure (.Fail _) => False

/-- The actual executed degree wrapper has the same complete native result,
represented through its failure latch. The input relation discharges absence
of a previous failure and of missing dense slots. -/
theorem decDeg_production_latched (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    ProductionLatchedUnitRel (decDeg node native) (cakeDecDeg node production) := by
  have monadic := decDeg_production_monadic node related
  generalize hn : decDeg node native = nativeResult at monadic ⊢
  rcases nativeResult with ⟨result, final⟩
  cases result with
  | success value =>
      cases value
      cases hp : cakeDecDegMonadic node production with
      | success value updated =>
          cases value
          simpa [ProductionUnitResultRel, hp, ProductionLatchedUnitRel,
            cakeDecDeg, related.failure, cakeDecDegStep] using monadic
      | failure error retained =>
          cases error <;> simp [ProductionUnitResultRel, hp] at monadic
  | failure error =>
      cases error with
      | Fail message =>
          cases hp : cakeDecDegMonadic node production <;>
            simp [ProductionUnitResultRel] at monadic
      | Subscript =>
          cases hp : cakeDecDegMonadic node production with
          | success value updated => simp [ProductionUnitResultRel, hp] at monadic
          | failure error retained =>
              cases error with
              | missingDegreeSlot => simp [ProductionUnitResultRel, hp] at monadic
              | subscript =>
                  simp only [ProductionUnitResultRel, hp] at monadic
                  have same : retained = production := by
                    unfold cakeDecDegMonadic at hp
                    split at hp
                    · split at hp <;> cases hp
                    · cases hp; rfl
                  subst retained
                  have cleared : {production with failure := none} = production := by
                    rw [← related.failure]
                  simpa [ProductionLatchedUnitRel, cakeDecDeg,
                    related.failure, cakeDecDegStep, hp, cleared] using
                    (And.intro rfl monadic :
                      (some CakeRaFailure.subscript : Option CakeRaFailure) = some .subscript ∧
                        ProductionStateRel final production)

end Flapjack.RegAlloc
