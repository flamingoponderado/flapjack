import Flapjack.Compiler.Backend.RegAlloc.ProductionMoveReset

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Parent equality is derived from the complete representation and original
validity, including the production BEq/native equality correspondence. This is
Flapjack actual/native query infrastructure, without a separate HOL original. -/
theorem isNotCoalesced_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    isNotCoalesced node native = (.success (cakeIsNotCoalesced production node), native) := by
  have parentBound : node < native.coalesced.length := by rwa [good.2.2.2.1]
  have value := related.parent_read node parentBound
  simp [isNotCoalesced, Translator.Monadic.MonadBase.bind, coalescedSubEqn,
    parentBound, holEl_eq_getElem node native.coalesced parentBound, ret,
    cakeIsNotCoalesced, value, Bool.beq_eq_decide_eq, eq_comm]

/-- The original validity discharges the actual optional move-flag read;
there is no supplied read result or successful lookup premise. -/
theorem moveRelatedSub_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    moveRelatedSub node native = (.success (cakeMoveRelatedSub production node), native) := by
  have moveBound : node < native.move_related.length := by rwa [good.2.2.2.2.1]
  have value := related.moveRelated_read node moveBound
  simp [moveRelatedSubEqn, moveBound, holEl_eq_getElem node native.move_related moveBound,
    cakeMoveRelatedSub, value]

/-- The actual consistency predicate agrees with native state reads and
short-circuit branches on original valid nodes, including cached adjacency.
All read values are derived; no consistency result is assumed. This untagged
transport is infrastructure, not a replacement native HOL theorem. -/
theorem consistencyOk_production (left right : Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (leftBound : left < native.dim) (rightBound : right < native.dim) :
    consistencyOk left right native =
      (.success (cakeConsistencyOk production left right), native) := by
  by_cases equal : left = right
  · simp [consistencyOk, equal, ret, cakeConsistencyOk]
  · have adjacencyBound : right < native.adj_ls.length := by rwa [good.1]
    have different : (left != right) = true := bne_iff_ne.mpr equal
    have adjacency := cakeAdjMem_production left right related good rightBound
    rw [holEl_eq_getElem right native.adj_ls adjacencyBound] at adjacency
    have fixedLeft := isFixed_production left related good leftBound
    have fixedRight := isFixed_production right related good rightBound
    have moveLeft := moveRelatedSub_production left related good leftBound
    have moveRight := moveRelatedSub_production right related good rightBound
    simp only [consistencyOk, if_neg equal, Translator.Monadic.MonadBase.bind,
      adjLsSubEqn, if_pos adjacencyBound, holEl_eq_getElem right native.adj_ls adjacencyBound]
    rw [← adjacency]
    cases query : cakeAdjMem production left right <;>
      simp [query, fixedLeft, fixedRight, moveLeft, moveRight,
        Translator.Monadic.MonadBase.bind, ret, cakeConsistencyOk, different,
        cakeMoveRelatedSub]

private theorem filterFold_reverse {α : Type} (predicate : α → Bool) (nodes acc : List α) :
    nodes.foldl (fun acc node => if predicate node then node :: acc else acc) acc =
      (nodes.filter predicate).reverse ++ acc := by
  induction nodes generalizing acc with
  | nil => simp
  | cons node rest ih =>
    cases selected : predicate node <;>
      simp [selected, ih, List.reverse_cons, List.append_assoc]

/-- Actual reversed filtering preserves the original state-filter order.
This is an unconditional list equation, with no independent HOL declaration. -/
theorem filterReversed_production {α : Type} (predicate : α → Bool) (nodes : List α) :
    filterReversed predicate nodes = (nodes.filter predicate).reverse := by
  simp [filterReversed, filterFold_reverse]

private theorem stateFilter_pure {α : Type} (predicate : α → M State Bool StateException)
    (pure : α → Bool) (nodes acc : List α) (state : State)
    (reads : ∀ node ∈ nodes, predicate node state = (.success (pure node), state)) :
    stExFilter predicate nodes acc state =
      (.success ((nodes.filter pure).reverse ++ acc), state) := by
  induction nodes generalizing acc with
  | nil => rfl
  | cons node rest ih =>
    simp only [stExFilter, Translator.Monadic.MonadBase.bind, reads node List.mem_cons_self]
    cases selected : pure node <;>
      simp only [Bool.false_eq_true, if_false, if_true,
        List.filter_cons, selected, List.reverse_cons, List.append_assoc, List.singleton_append]
    all_goals exact ih _ (fun next member => reads next (List.mem_cons_of_mem node member))

private theorem statePartition_pure {α : Type} (predicate : α → M State Bool StateException)
    (pure : α → Bool) (nodes yes no : List α) (state : State)
    (reads : ∀ node ∈ nodes, predicate node state = (.success (pure node), state)) :
    stExPartition predicate nodes yes no state =
      (.success (holPart pure nodes yes no), state) := by
  induction nodes generalizing yes no with
  | nil => rfl
  | cons node rest ih =>
    simp only [stExPartition, Translator.Monadic.MonadBase.bind, reads node List.mem_cons_self]
    cases selected : pure node <;>
      simp only [Bool.false_eq_true, if_false, if_true, holPart, selected]
    all_goals exact ih _ _ (fun next member => reads next (List.mem_cons_of_mem node member))


/-- The complete actual prefreeze phase has the native Boolean result and
represents every post-state field. Both original worklist filters, the move
consistency filter, bulk reset, move partition, and simplify continuation are
proved in source order. All filtered domains and intermediate good states are
derived from the original invariant, not supplied target results. This is
actual/native infrastructure, not another HOL do_prefreeze_success port. -/
theorem doPrefreeze_production (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result : State,
      doPrefreeze limit native = (.success (cakeDoPrefreeze limit production).1, result) ∧
      ProductionStateRel result (cakeDoPrefreeze limit production).2 := by
  have originalGood := good
  obtain ⟨a,b,c,d,e,f,g,h,simpBounds,spillBounds,freezeBounds,availableBounds,
    unavailableBounds,undirected⟩ := good
  let parentPredicate := fun node => cakeIsNotCoalesced production node
  let freeze := (native.freeze_wl.filter parentPredicate).reverse
  let spill := (native.spill_wl.filter parentPredicate).reverse
  have freezeRun : stExFilter isNotCoalesced native.freeze_wl [] native =
      (.success freeze, native) := by
    simpa only [List.append_nil] using stateFilter_pure _ parentPredicate _ [] native
      (fun node member => isNotCoalesced_production node related originalGood (freezeBounds node member))
  have spillRun : stExFilter isNotCoalesced native.spill_wl [] native =
      (.success spill, native) := by
    simpa only [List.append_nil] using stateFilter_pure _ parentPredicate _ [] native
      (fun node member => isNotCoalesced_production node related originalGood (spillBounds node member))
  have actualFreeze : filterReversed parentPredicate production.freezeWl = freeze := by
    rw [filterReversed_production, related.freeze]
  have actualSpill : filterReversed parentPredicate production.spillWl = spill := by
    rw [filterReversed_production, related.spill]
  have freezeBound : ∀ node ∈ freeze, node < native.dim := by
    intro node member
    exact freezeBounds node (List.mem_filter.mp (List.mem_reverse.mp member)).1
  have spillBound : ∀ node ∈ spill, node < native.dim := by
    intro node member
    exact spillBounds node (List.mem_filter.mp (List.mem_reverse.mp member)).1
  let first : State := {native with spill_wl := spill}
  let actualFirst : CakeRaState := {production with spillWl := spill}
  have firstRel : ProductionStateRel first actualFirst := {related with spill := rfl}
  have goodFirst : goodRaState first :=
    ⟨a,b,c,d,e,f,g,h,simpBounds,spillBound,freezeBounds,availableBounds,unavailableBounds,undirected⟩
  let consistencyPredicate := fun (move : Nat × (Nat × Nat)) =>
    cakeConsistencyOk actualFirst move.2.1 move.2.2
  let moves := (native.unavail_moves_wl.filter consistencyPredicate).reverse
  have consistencyRun : stExFilter (fun move : Nat × (Nat × Nat) =>
      consistencyOk move.2.1 move.2.2) native.unavail_moves_wl [] first =
      (.success moves, first) := by
    apply (stateFilter_pure _ consistencyPredicate _ [] first ?_).trans
      (by simp only [List.append_nil]; rfl)
    intro move member
    have bounds := unavailableBounds move member
    exact consistencyOk_production _ _ firstRel goodFirst bounds.1 bounds.2
  have actualMoves : filterReversed consistencyPredicate actualFirst.unavailMovesWl = moves := by
    rw [filterReversed_production, related.unavailableMoves]
  dsimp only [first] at consistencyRun
  dsimp only [actualFirst, consistencyPredicate] at actualMoves
  have movesBound : ∀ move ∈ moves, move.2.1 < native.dim ∧ move.2.2 < native.dim := by
    intro move member
    exact unavailableBounds move (List.mem_filter.mp (List.mem_reverse.mp member)).1
  obtain ⟨reset, resetRun, resetRel⟩ := resetMoveRelated_production moves firstRel goodFirst movesBound
  obtain ⟨flags, nativeReset, flagsLength⟩ := resetMoveRelatedSuccess moves first ⟨goodFirst, movesBound⟩
  dsimp only [first] at nativeReset
  have resetShape : reset = {first with move_related := flags} :=
    congrArg Prod.snd (resetRun.symm.trans nativeReset)
  subst reset
  let second : State := {first with move_related := flags, unavail_moves_wl := moves}
  let actualSecond : CakeRaState := {cakeResetMoveRelated moves actualFirst with unavailMovesWl := moves}
  have secondRel : ProductionStateRel second actualSecond := {resetRel with unavailableMoves := rfl}
  have goodSecond : goodRaState second :=
    ⟨a,b,c,d,flagsLength,f,g,h,simpBounds,spillBound,freezeBounds,availableBounds,movesBound,undirected⟩
  let movePredicate := fun node => cakeMoveRelatedSub actualSecond node
  let parts := holPartition movePredicate freeze
  have partitionRun : stExPartition moveRelatedSub freeze [] [] second =
      (.success parts, second) := statePartition_pure _ movePredicate _ [] [] second
        (fun node member => moveRelatedSub_production node secondRel goodSecond (freezeBound node member))
  dsimp only [first, second] at partitionRun
  have partBound : ∀ node, (node ∈ parts.1 ∨ node ∈ parts.2) → node < native.dim := by
    intro node member
    have membership : node ∈ freeze ∨ node ∈ ([] : List Nat) := by
      rcases member with member | member
      · exact (mem_holPart movePredicate freeze [] [] node).1 member
      · exact (mem_holPart movePredicate freeze [] [] node).2 member
    rcases membership with member | member
    · exact freezeBound node member
    · cases member
  let prepared : State := {second with
    simp_wl := parts.2 ++ second.simp_wl
    freeze_wl := parts.1}
  let actualPrepared : CakeRaState := {actualSecond with
    simpWl := parts.2 ++ actualSecond.simpWl
    freezeWl := parts.1}
  have preparedRel : ProductionStateRel prepared actualPrepared :=
    {secondRel with
      simplify := congrArg (parts.2 ++ ·) secondRel.simplify
      freeze := rfl}
  have goodPrepared : goodRaState prepared := by
    refine ⟨a,b,c,d,flagsLength,f,g,h,?_,spillBound,?_,availableBounds,movesBound,undirected⟩
    · intro node member
      rcases List.mem_append.mp member with member | member
      · exact partBound node (Or.inr member)
      · exact simpBounds node member
    · intro node member
      exact partBound node (Or.inl member)
  obtain ⟨result, simplifyRun, finalRel⟩ := doSimplify_production limit preparedRel goodPrepared
  have actual : cakeDoPrefreeze limit production = cakeDoSimplify limit actualPrepared := by
    unfold cakeDoPrefreeze
    rw [actualFreeze, actualSpill]
    dsimp only
    rw [actualMoves, partitionReversed_production]
    rfl
  refine ⟨result, ?_, ?_⟩
  · rw [actual]
    simp only [doPrefreeze, Translator.Monadic.MonadBase.bind, getFreezeWl, freezeRun,
      getSpillWl, spillRun, ignoreBind, setSpillWl, getUnavailMovesWl, consistencyRun,
      nativeReset, setUnavailMovesWl, partitionRun, addSimpWl, getSimpWl, setSimpWl, setFreezeWl]
    exact simplifyRun
  · simpa only [actual] using finalRel

end Flapjack.RegAlloc
