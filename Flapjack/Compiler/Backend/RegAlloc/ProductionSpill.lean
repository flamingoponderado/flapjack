import Flapjack.Compiler.Backend.RegAlloc.ProductionSpillChoice

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem singleton_action {action : Nat → M State Unit StateException}
    (node : Nat) (state : State) : stExForeach [node] action state = action node state := by
  simp only [stExForeach, ignoreBind, ret]
  cases action node state with
  | mk result final =>
    cases result with
    | success payload => cases payload; rfl
    | failure error => rfl

/-- The spill continuation represents every final state field after the
selected node is decremented/pushed and its remaining worklist installed.
Selection bounds are consumed here; the complete phase derives them from the
original invariant. This is actual/native infrastructure without a HOL tag. -/
theorem spillContinuation_production (limit node : Nat) (remaining : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) (remainingBound : ∀ next ∈ remaining, next < native.dim) :
    ∃ result,
      ignoreBind (decDegree node) (ignoreBind (pushStack node)
        (ignoreBind (setSpillWl remaining) (ignoreBind (unspill limit) (ret true)))) native =
        (.success true, result) ∧
      ProductionStateRel result
        (cakeUnspill limit {cakePushStack node (cakeDecDegree node production) with spillWl := remaining}) := by
  obtain ⟨degrees, degreeRun, degreeLength, degreeRel⟩ :=
    decDegree_foreach_production [node] related good
  rw [singleton_action] at degreeRun
  have degreeRelated : ProductionStateRel {native with degrees := degrees}
      (cakeDecDegree node production) := by
    simpa only [List.foldl_cons, List.foldl_nil] using degreeRel
  have goodDegrees : goodRaState {native with degrees := degrees} := by
    obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
    exact ⟨a,b,degreeLength.trans c,d,e,f,g,h,i,j,k,l,m,n⟩
  obtain ⟨pushed, pushRun, pushRel⟩ := pushStack_foreach_production [node]
    degreeRelated goodDegrees (by simpa using bound)
  rw [singleton_action] at pushRun
  have pushedRelated : ProductionStateRel pushed
      (cakePushStack node (cakeDecDegree node production)) := by
    simpa only [List.foldl_cons, List.foldl_nil] using pushRel
  obtain ⟨finalDegrees, flags, stack, nativePush, degreeSize, flagSize⟩ :=
    pushStackSuccess [node] {native with degrees := degrees} ⟨by simpa using bound, goodDegrees⟩
  rw [singleton_action] at nativePush
  have pushedShape := congrArg Prod.snd (pushRun.symm.trans nativePush)
  simp only at pushedShape
  subst pushed
  have goodPush : goodRaState {native with degrees := finalDegrees, move_related := flags, stack := stack} := by
    obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
    exact ⟨a,b,degreeSize.trans (degreeLength.trans c),d,flagSize.trans e,f,g,h,i,j,k,l,m,n⟩
  have goodRemaining : goodRaState
      {native with degrees := finalDegrees, move_related := flags, stack := stack, spill_wl := remaining} := by
    obtain ⟨a,b,c,d,e,f,g,h,i,_,k,l,m,n⟩ := goodPush
    exact ⟨a,b,c,d,e,f,g,h,i,remainingBound,k,l,m,n⟩
  have remainingRelated : ProductionStateRel
      {native with degrees := finalDegrees, move_related := flags, stack := stack, spill_wl := remaining}
      {cakePushStack node (cakeDecDegree node production) with spillWl := remaining} :=
    {pushedRelated with spill := rfl}
  obtain ⟨result, unspillRun, finalRel⟩ := unspill_production limit remainingRelated goodRemaining
  refine ⟨result, ?_, finalRel⟩
  simp only [ignoreBind, degreeRun, pushRun, setSpillWl, unspillRun, ret]

/-- Whole actual spill correspondence for optional costs produced from the
same source associations. The tree/array cost codec is proved, not assumed;
candidate bounds and intermediate valid states are derived. This infrastructure
does not assert whole allocator initialization or coalescing correspondence. -/
theorem doSpill_production (entries : Option (NatInfoMap Nat)) (limit : Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result,
      doSpill (entries.map sptFromAList) limit native =
        (.success (cakeDoSpill (entries.map (cakeSpillCostMap production.dim)) limit production).1, result) ∧
      ProductionStateRel result
        (cakeDoSpill (entries.map (cakeSpillCostMap production.dim)) limit production).2 := by
  cases spills : native.spill_wl with
  | nil =>
    have empty : production.spillWl = [] := related.spill.trans spills
    refine ⟨native, ?_, ?_⟩
    · simp [doSpill, Translator.Monadic.MonadBase.bind, getSpillWl, getDim, spills,
        cakeDoSpill, empty, ret]
    · simpa [cakeDoSpill, empty] using related
  | cons node rest =>
    have nodeBound : node < native.dim := good.2.2.2.2.2.2.2.2.2.1 node (by simp [spills])
    have restBound : ∀ next ∈ rest, next < native.dim := by
      intro next member
      exact good.2.2.2.2.2.2.2.2.2.1 next (by rw [spills]; exact List.mem_cons_of_mem node member)
    have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
    have read := related.degree_read node degreeBound
    let choice := match entries with
      | none => cakeStExListMaxDeg production.degrees rest native.dim node native.degrees[node] []
      | some costs => cakeStExListMinCost production.degrees (cakeSpillCostMap production.dim costs)
          rest native.dim node (safeDiv ((cakeSpillCostMap production.dim costs).get node |>.getD 0) native.degrees[node]) []
    have choiceBound : choice.1 < native.dim ∧ ∀ next ∈ choice.2, next < native.dim := by
      cases entries with
      | none => exact cakeStExListMaxDeg_bounds _ _ _ _ _ _ restBound (by simp) nodeBound
      | some costs => exact cakeStExListMinCost_bounds _ _ _ _ _ _ _ restBound (by simp) nodeBound
    have selectorRun :
        (match entries.map sptFromAList with
          | none => stExListMaxDeg rest native.dim node native.degrees[node] []
          | some costs => stExListMinCost costs rest native.dim node
              (safeDiv (lookupAny node costs 0) native.degrees[node]) []) native =
        (.success choice, native) := by
      cases entries with
      | none => exact stExListMaxDeg_production _ _ _ _ related good
      | some costs =>
        have costRead : ((cakeSpillCostMap production.dim costs).get node).getD 0 =
            lookupAny node (sptFromAList costs) 0 := by
          rw [cakeSpillCostMap_production production.dim costs node]
          cases eq : sptLookup node (sptFromAList costs) <;> simp [lookupAny, eq]
        simpa only [Option.map_some, choice, costRead] using
          stExListMinCost_production (sptFromAList costs) (cakeSpillCostMap production.dim costs)
            (cakeSpillCostMap_production production.dim costs) rest node
            (safeDiv (lookupAny node (sptFromAList costs) 0) native.degrees[node]) [] related good
    obtain ⟨result, continuationRun, finalRel⟩ := spillContinuation_production limit choice.1 choice.2
      related good choiceBound.1 choiceBound.2
    have actual : cakeDoSpill (entries.map (cakeSpillCostMap production.dim)) limit production =
        (true, cakeUnspill limit
          {cakePushStack choice.1 (cakeDecDegree choice.1 production) with spillWl := choice.2}) := by
      simp only [cakeDoSpill, related.spill, spills, read, Option.getD_some]
      cases entries <;> simp only [Option.map_none, Option.map_some, choice,
        related.dimension, cakeSafeDiv]
    refine ⟨result, ?_, ?_⟩
    · rw [actual]
      simp only [doSpill, Translator.Monadic.MonadBase.bind, getSpillWl, getDim, spills,
        degreesSubEqn, if_pos degreeBound, holEl_eq_getElem node native.degrees degreeBound]
      cases entries <;> simp only [Option.map_none, Option.map_some] at selectorRun ⊢
      all_goals rw [selectorRun]; exact continuationRun
    · simpa only [actual] using finalRel

end Flapjack.RegAlloc
