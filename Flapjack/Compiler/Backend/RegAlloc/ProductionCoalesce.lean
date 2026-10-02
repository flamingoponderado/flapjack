import Flapjack.Compiler.Backend.RegAlloc.ProductionBgOk

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Actual respill preserves the native unit result and complete post-state
relation. The original degree domain is derived; natural-list contains and
filter equality are exact. This is actual/native infrastructure, without a
separate HOL original. -/
theorem respill_production (limit node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    ∃ result, respill limit node native = (.success (), result) ∧
      ProductionStateRel result (cakeRespill limit node production) := by
  have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
  have read := related.degree_read node degreeBound
  by_cases low : native.degrees[node] < limit
  · refine ⟨native, ?_, ?_⟩
    · simp [respill, Translator.Monadic.MonadBase.bind, degreesSubEqn, degreeBound,
        holEl_eq_getElem node native.degrees degreeBound, low, ret]
    · simpa [cakeRespill, read, low] using related
  · by_cases member : node ∈ native.freeze_wl
    · let result : State := {native with
        spill_wl := node :: native.spill_wl
        freeze_wl := native.freeze_wl.filter (fun next => decide (next ≠ node))}
      have actual : cakeRespill limit node production =
          {production with
            spillWl := node :: production.spillWl
            freezeWl := production.freezeWl.filter (fun next => decide (next ≠ node))} := by
        simp [cakeRespill, read, low, related.freeze, member, cakeAddSpillWl]
      refine ⟨result, ?_, ?_⟩
      · simp [respill, Translator.Monadic.MonadBase.bind, degreesSubEqn, degreeBound,
          holEl_eq_getElem node native.degrees degreeBound, low, getFreezeWl, member,
          ignoreBind, addSpillWl, getSpillWl, setSpillWl, setFreezeWl, result]
      · rw [actual]
        exact {related with spill := by simp [related.spill, result], freeze := by simp [related.freeze, result]}
    · refine ⟨native, ?_, ?_⟩
      · simp [respill, Translator.Monadic.MonadBase.bind, degreesSubEqn, degreeBound,
          holEl_eq_getElem node native.degrees degreeBound, low, getFreezeWl, member, ret]
      · simpa [cakeRespill, read, low, related.freeze, member] using related

private theorem parent_step (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    ∃ result, coalesceParent node native = (.success (cakeCoalesceParent node production).1, result) ∧
      goodRaState result ∧ result.dim = native.dim ∧ (cakeCoalesceParent node production).1 < native.dim ∧
      ProductionStateRel result (cakeCoalesceParent node production).2 := by
  obtain ⟨result, run, represented⟩ := coalesceParent_production node related good bound
  obtain ⟨root, source, parents, sourceRun, rootBound, sourceGood, sourceShape⟩ :=
    coalesceParentSuccess node native ⟨bound, good⟩
  have equality := Prod.mk.inj (run.symm.trans sourceRun)
  have rootEq := Exc.success.inj equality.1
  refine ⟨result, run, equality.2 ▸ sourceGood, ?_, ?_, represented⟩
  · rw [equality.2, sourceShape]
  · rwa [rootEq]

/-- The complete actual move chooser preserves the native optional selected
move/case payload, pending moves, and full post-state. Parent-compression
domains and canonical endpoint bounds are derived from the original invariant.
Unavailable accumulators are not read, so this correspondence needs no bounds
on their contents. This is actual/native infrastructure, without a HOL tag. -/
theorem stExFirst_production (limit : Nat) (moves unavailable : List (Nat × (Nat × Nat)))
    {native : State} {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (bounds : ∀ move ∈ moves, move.2.1 < native.dim ∧ move.2.2 < native.dim) :
    ∃ result,
      stExFirst consistencyOk (bgOk limit) moves unavailable native =
        (.success ((cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
          production moves unavailable).1,
          (cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
          production moves unavailable).2.1), result) ∧
      goodRaState result ∧ result.dim = native.dim ∧
      ProductionStateRel result (cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
        production moves unavailable).2.2 := by
  induction moves generalizing native production unavailable with
  | nil =>
    refine ⟨native, ?_, good, rfl, ?_⟩
    · simp [stExFirst, cakeStExFirst, ret]
    · simpa only [cakeStExFirst] using related
  | cons move rest ih =>
    obtain ⟨priority, u, v⟩ := move
    have endpoints := bounds (priority, (u, v)) (by simp)
    obtain ⟨first, firstRun, firstGood, firstDim, rootXBound, firstRel⟩ := parent_step u related good endpoints.1
    let actualFirst := cakeCoalesceParent u production
    have vBound : v < first.dim := by rw [firstDim]; exact endpoints.2
    obtain ⟨second, secondRun, secondGood, secondDim, rootYBound, secondRel⟩ := parent_step v firstRel firstGood vBound
    let actualSecond := cakeCoalesceParent v actualFirst.2
    have xBound : actualFirst.1 < second.dim := by rw [secondDim, firstDim]; exact rootXBound
    have yBound : actualSecond.1 < second.dim := by rw [secondDim]; exact rootYBound
    have tailBounds : ∀ move ∈ rest, move.2.1 < second.dim ∧ move.2.2 < second.dim := by
      intro move member
      rw [secondDim, firstDim]
      exact bounds move (List.mem_cons_of_mem _ member)
    have consistencyRun := consistencyOk_production actualFirst.1 actualSecond.1 secondRel secondGood xBound yBound
    dsimp only [actualFirst, actualSecond] at consistencyRun
    cases consistent : cakeConsistencyOk (cakeCoalesceParent v (cakeCoalesceParent u production).2).2
        (cakeCoalesceParent u production).1 (cakeCoalesceParent v (cakeCoalesceParent u production).2).1 with
    | false =>
      obtain ⟨result, run, resultGood, resultDim, represented⟩ := ih unavailable secondRel secondGood tailBounds
      have actual : cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
          production ((priority, (u, v)) :: rest) unavailable =
          cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state) actualSecond.2 rest unavailable := by
        rw [cakeStExFirst]
        simp only [consistent, Bool.not_false, if_true]
        rfl
      refine ⟨result, ?_, resultGood, resultDim.trans (secondDim.trans firstDim), ?_⟩
      · rw [actual, stExFirst]
        simp [Translator.Monadic.MonadBase.bind, firstRun, secondRun, consistencyRun, consistent, actualFirst, actualSecond, run]
      · simpa only [actual] using represented
    | true =>
      let canonical := cakeCanonizeMove actualSecond.2 actualFirst.1 actualSecond.1
      have canonicalRun := canonizeMove_production actualFirst.1 actualSecond.1 secondRel secondGood xBound yBound
      obtain ⟨cx, cy, sourceCanonical, cxBound, cyBound⟩ :=
        canonizeMoveSuccess actualFirst.1 actualSecond.1 second ⟨xBound, yBound, secondGood⟩
      have canonicalEq := Exc.success.inj (congrArg Prod.fst (canonicalRun.symm.trans sourceCanonical))
      change canonical = (cx, cy) at canonicalEq
      have canonicalBounds : canonical.1 < second.dim ∧ canonical.2 < second.dim := by
        simpa only [canonicalEq] using And.intro cxBound cyBound
      have bgRun := bgOk_production limit canonical.1 canonical.2 secondRel secondGood canonicalBounds.1 canonicalBounds.2
      dsimp only [actualFirst, actualSecond, canonical] at canonicalRun bgRun
      cases choice : cakeBgOk limit canonical.1 canonical.2 actualSecond.2 with
      | none =>
        obtain ⟨result, run, resultGood, resultDim, represented⟩ :=
          ih ((priority, canonical) :: unavailable) secondRel secondGood tailBounds
        have actual : cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
            production ((priority, (u, v)) :: rest) unavailable =
            cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
              actualSecond.2 rest ((priority, canonical) :: unavailable) := by
          rw [cakeStExFirst]
          simp only [consistent, Bool.not_true, Bool.false_eq_true, if_false]
          change (match cakeBgOk limit canonical.1 canonical.2 actualSecond.2 with | none => _ | some _ => _) = _
          rw [choice]
        refine ⟨result, ?_, resultGood, resultDim.trans (secondDim.trans firstDim), ?_⟩
        · dsimp only [actualFirst, actualSecond, canonical] at choice ⊢
          rw [actual, stExFirst]
          simp [Translator.Monadic.MonadBase.bind, firstRun, secondRun, consistencyRun,
            consistent, canonicalRun, bgRun, choice, actualFirst, actualSecond, canonical, run]
        · simpa only [actual] using represented
      | some payload =>
        have actual : cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
            production ((priority, (u, v)) :: rest) unavailable =
            (some (canonical, payload, rest), unavailable, actualSecond.2) := by
          rw [cakeStExFirst]
          simp only [consistent, Bool.not_true, Bool.false_eq_true, if_false]
          change (match cakeBgOk limit canonical.1 canonical.2 actualSecond.2 with | none => _ | some _ => _) = _
          rw [choice]
        refine ⟨second, ?_, secondGood, secondDim.trans firstDim, ?_⟩
        · dsimp only [actualFirst, actualSecond, canonical] at choice ⊢
          rw [actual, stExFirst]
          simp [Translator.Monadic.MonadBase.bind, firstRun, secondRun, consistencyRun,
            consistent, canonicalRun, bgRun, choice, actualFirst, actualSecond, canonical, ret]
        · simpa only [actual] using secondRel

/-- Complete actual coalescing phase correspondence. All intermediate bounds
and invariants follow from the original good state and native source lemmas.
This connects the executed array allocator to native semantics and has no
separate HOL original. -/
theorem doCoalesce_production (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result, doCoalesce limit native = (.success (cakeDoCoalesce limit production).1, result) ∧
      ProductionStateRel result (cakeDoCoalesce limit production).2 := by
  have available := good.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨chosen, run, chosenGood, chosenDim, chosenRel⟩ :=
    stExFirst_production limit native.avail_moves_wl [] related good available
  let actual := cakeStExFirst cakeConsistencyOk (fun state x y => cakeBgOk limit x y state)
    production native.avail_moves_wl []
  obtain ⟨ores, pending, source, parents, sourceRun, sourceGood, sourceShape, pendingBounds, selectionBounds⟩ :=
    stExFirstConsistencyOkBgOk limit native.avail_moves_wl [] native
      ⟨good, available, fun _ member => by cases member⟩
  have equality := Prod.mk.inj (run.symm.trans sourceRun)
  have outputEq := Exc.success.inj equality.1
  have selected : actual.1 = ores := congrArg Prod.fst outputEq
  have pendingEq : actual.2.1 = pending := congrArg Prod.snd outputEq
  have chooserRun : stExFirst consistencyOk (bgOk limit) native.avail_moves_wl [] native =
      (.success (ores, pending), chosen) := by
    change stExFirst consistencyOk (bgOk limit) native.avail_moves_wl [] native =
      (.success (actual.1, actual.2.1), chosen) at run
    simpa only [selected, pendingEq] using run
  have chosenShape : chosen = {native with coalesced := parents} := equality.2.trans sourceShape
  have allPending : ∀ move ∈ pending ++ chosen.unavail_moves_wl,
      move.2.1 < chosen.dim ∧ move.2.2 < chosen.dim := by
    intro move member
    rcases List.mem_append.mp member with member | member
    · rw [chosenDim]; exact pendingBounds move member
    · exact chosenGood.2.2.2.2.2.2.2.2.2.2.2.2.1 move member
  dsimp only [actual] at selected pendingEq
  cases ores with
  | none =>
    refine ⟨{chosen with unavail_moves_wl := pending ++ chosen.unavail_moves_wl, avail_moves_wl := []}, ?_, ?_⟩
    · simp [doCoalesce, Translator.Monadic.MonadBase.bind, ignoreBind, getAvailMovesWl,
        chooserRun, cakeDoCoalesce, related.availableMoves, selected, pendingEq,
        addUnavailMovesWl, getUnavailMovesWl, setUnavailMovesWl, setAvailMovesWl, ret]
    · have rel : ProductionStateRel
          {chosen with unavail_moves_wl := actual.2.1 ++ chosen.unavail_moves_wl, avail_moves_wl := []}
          {(cakeAddUnavailMovesWl actual.2.1 actual.2.2) with availMovesWl := []} :=
        {chosenRel with
          availableMoves := rfl,
          unavailableMoves := by simp [cakeAddUnavailMovesWl, actual, chosenRel.unavailableMoves]}
      simpa only [cakeDoCoalesce, related.availableMoves, selected, actual, pendingEq] using rel
  | some selection =>
    obtain ⟨⟨x, y⟩, ⟨case1, case2⟩, rest⟩ := selection
    obtain ⟨xBound, yBound, case1Bounds, case2Bounds, restBounds⟩ := selectionBounds
    let prepared : State := {chosen with
      unavail_moves_wl := pending ++ chosen.unavail_moves_wl
      avail_moves_wl := rest}
    let preparedActual : CakeRaState := {cakeAddUnavailMovesWl actual.2.1 actual.2.2 with availMovesWl := rest}
    have preparedRel : ProductionStateRel prepared preparedActual :=
      {chosenRel with
        availableMoves := rfl
        unavailableMoves := by simp [prepared, preparedActual, cakeAddUnavailMovesWl, actual, pendingEq, chosenRel.unavailableMoves]}
    have preparedGood : goodRaState prepared := by
      obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := chosenGood
      exact ⟨a,b,c,d,e,f,g,h,i,j,k,
        fun move member => by simpa only [prepared, chosenDim] using restBounds move member, allPending,n⟩
    have xb : x < prepared.dim := by simpa only [prepared, chosenDim] using xBound
    have yb : y < prepared.dim := by simpa only [prepared, chosenDim] using yBound
    have cb1 : ∀ node ∈ case1, node < prepared.dim := by simpa only [prepared, chosenDim] using case1Bounds
    have cb2 : ∀ node ∈ case2, node < prepared.dim := by simpa only [prepared, chosenDim] using case2Bounds
    obtain ⟨merged, mergeRun, mergedRel⟩ :=
      doCoalesceReal_production x y case1 case2 preparedRel preparedGood xb yb cb1 cb2
    obtain ⟨sourceMerged, sourceMergeRun, mergedGood, _, mergeDim, _⟩ :=
      doCoalesceRealSuccess x y case1 case2 prepared ⟨yb, xb, cb1, cb2, preparedGood⟩
    have mergedEq := congrArg Prod.snd (mergeRun.symm.trans sourceMergeRun)
    change merged = sourceMerged at mergedEq
    have mg : goodRaState merged := mergedEq.symm ▸ mergedGood
    have md : prepared.dim = merged.dim := by simpa only [mergedEq] using mergeDim
    obtain ⟨unspilled, unspillRun, unspilledRel⟩ := unspill_production limit mergedRel mg
    obtain ⟨sourceUnspilled, _, sourceUnspillRun, unspilledGood, _, unspillDim, _⟩ :=
      unspillSuccess (α := Unit) limit merged mg
    have unspilledEq := congrArg Prod.snd (unspillRun.symm.trans sourceUnspillRun)
    change unspilled = sourceUnspilled at unspilledEq
    have ug : goodRaState unspilled := unspilledEq.symm ▸ unspilledGood
    have ud : merged.dim = unspilled.dim := by simpa only [unspilledEq] using unspillDim
    obtain ⟨result, respillRun, resultRel⟩ := respill_production limit x unspilledRel ug
      (by rw [← ud, ← md]; exact xb)
    refine ⟨result, ?_, ?_⟩
    · simp [doCoalesce, Translator.Monadic.MonadBase.bind, ignoreBind, getAvailMovesWl,
        chooserRun, cakeDoCoalesce, related.availableMoves, selected, pendingEq,
        addUnavailMovesWl, getUnavailMovesWl, setUnavailMovesWl, setAvailMovesWl,
        prepared, mergeRun, unspillRun, respillRun, ret]
    · simpa only [cakeDoCoalesce, related.availableMoves, selected, actual, preparedActual] using resultRel

end Flapjack.RegAlloc
