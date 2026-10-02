import Flapjack.Compiler.Backend.RegAlloc.ProductionCoalesceReal

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Actual recursive parent compression returns the native root and preserves
the complete post-state relation. Every parent and tag read is justified by
the original invariant; recursive post-state bounds follow from the checked
native success theorem. This is actual/native infrastructure, not another
HOL coalesce_parent_success port. -/
theorem coalesceParent_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    ∃ result, coalesceParent node native = (.success (cakeCoalesceParent node production).1, result) ∧
      ProductionStateRel result (cakeCoalesceParent node production).2 := by
  induction node using Nat.strongRecOn generalizing native production with
  | ind node ih =>
    have parentBound : node < native.coalesced.length := by rwa [good.2.2.2.1]
    let parent := native.coalesced[node]
    have read := related.parent_read node parentBound
    have parentNodeBound : parent < native.dim := good.2.2.2.2.2.1 parent (List.getElem_mem parentBound)
    have fixedRun := isFixed_production parent related good parentNodeBound
    dsimp only [parent] at fixedRun
    by_cases fixed : cakeIsFixed production native.coalesced[node]
    · have actual : cakeCoalesceParent node production = (parent, production) := by
        rw [cakeCoalesceParent]
        simp [read, fixed, parent]
      refine ⟨native, ?_, by simpa only [actual] using related⟩
      rw [actual, coalesceParent]
      simp [Translator.Monadic.MonadBase.bind, coalescedSubEqn, parentBound,
        holEl_eq_getElem node native.coalesced parentBound, fixedRun, fixed, ret, parent]
    · by_cases forward : node ≤ native.coalesced[node]
      · have actual : cakeCoalesceParent node production = (node, production) := by
          rw [cakeCoalesceParent]
          simp [read, fixed, forward]
        refine ⟨native, ?_, by simpa only [actual] using related⟩
        rw [actual, coalesceParent]
        simp [Translator.Monadic.MonadBase.bind, coalescedSubEqn, parentBound,
          holEl_eq_getElem node native.coalesced parentBound, fixedRun, fixed, forward, ret]
      · obtain ⟨next, nextRun, nextRel⟩ := ih parent (by omega) related good parentNodeBound
        obtain ⟨root, sourceNext, parents, sourceRun, _, sourceGood, sourceShape⟩ :=
          coalesceParentSuccess parent native ⟨parentNodeBound, good⟩
        have equality := Prod.mk.inj (nextRun.symm.trans sourceRun)
        have nextGood : goodRaState next := equality.2 ▸ sourceGood
        have nextDim : next.dim = native.dim := by
          rw [equality.2, sourceShape]
        have nextParentBound : node < next.coalesced.length := by
          rw [nextGood.2.2.2.1, nextDim]
          exact bound
        dsimp only [parent] at nextRun
        let actualNext := cakeCoalesceParent parent production
        have actual : cakeCoalesceParent node production =
            (actualNext.1, {actualNext.2 with coalesced := actualNext.2.coalesced.set node actualNext.1}) := by
          rw [cakeCoalesceParent]
          simp [read, fixed, forward, actualNext, parent]
        refine ⟨{next with coalesced := next.coalesced.set node actualNext.1}, ?_, ?_⟩
        · rw [actual, coalesceParent]
          simp [Translator.Monadic.MonadBase.bind, coalescedSubEqn, parentBound,
            holEl_eq_getElem node native.coalesced parentBound, fixedRun, fixed,
            forward, nextRun, ignoreBind, updateCoalescedEqn, nextParentBound, ret,
            actualNext, parent]
        · simpa only [actual] using nextRel.parent_write node actualNext.1 nextParentBound

/-- Canonical move ordering agrees on both Fixed endpoints and on the numeric
tie/order cases. Tag reads are discharged from the original invariant. This
is actual/native query infrastructure without a separate HOL original. -/
theorem canonizeMove_production (x y : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (xBound : x < native.dim) (yBound : y < native.dim) :
    canonizeMove x y native = (.success (cakeCanonizeMove production x y), native) := by
  have xRead := isFixed_production x related good xBound
  have yRead := isFixed_production y related good yBound
  simp only [canonizeMove, Translator.Monadic.MonadBase.bind, xRead, yRead, cakeCanonizeMove]
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> rfl

end Flapjack.RegAlloc
