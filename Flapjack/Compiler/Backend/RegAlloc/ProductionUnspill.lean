import Flapjack.Compiler.Backend.RegAlloc.ProductionMoveRevival

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Source state validity discharges every actual degree/parent read. This
query equation is cross-implementation infrastructure, without a HOL tag. -/
theorem splitDegree_production (limit : Nat) (node : Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) :
    splitDegree native.dim limit node native =
      (.success (cakeSplitDegree production native.dim limit node), native) := by
  by_cases bound : node < native.dim
  · have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
    have parentBound : node < native.coalesced.length := by rwa [good.2.2.2.1]
    have degreeRead := related.degree_read node degreeBound
    have parentRead := related.parent_read node parentBound
    simp [splitDegree, Translator.Monadic.MonadBase.bind, degreesSubEqn,
      coalescedSubEqn, isNotCoalesced, ret, bound, degreeBound, parentBound,
      holEl_eq_getElem node native.degrees degreeBound,
      holEl_eq_getElem node native.coalesced parentBound,
      cakeSplitDegree, cakeIsNotCoalesced, degreeRead, parentRead, Bool.beq_eq_decide_eq, eq_comm]
  · simp [splitDegree, cakeSplitDegree, bound, ret]

private theorem statePartition_pure {α : Type} (nodes yes no : List α)
    (predicate : α → M State Bool StateException) (pure : α → Bool) (state : State)
    (reads : ∀ node ∈ nodes, predicate node state = (.success (pure node), state)) :
    stExPartition predicate nodes yes no state =
      (.success (holPart pure nodes yes no), state) := by
  induction nodes generalizing yes no with
  | nil => rfl
  | cons node rest ih =>
    simp only [stExPartition, Translator.Monadic.MonadBase.bind, reads node List.mem_cons_self]
    cases choice : pure node <;>
      simp only [Bool.false_eq_true, if_false, if_true,
        holPart, choice]
    all_goals exact ih _ _ (fun next member => reads next (List.mem_cons_of_mem node member))

/-- Both actual unspill partitions, the intermediate move revival, and every
final state field agree with native unspill. Success and all lookup domains
are proved from the original good_ra_state invariant; no target evaluation
or desired result is assumed. This actual/native transport has no separate
HOL original, and is not a duplicate of native unspill_success. -/
theorem unspill_production (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result : State, unspill limit native = (.success (), result) ∧
      ProductionStateRel result (cakeUnspill limit production) := by
  let degreePredicate := fun node => cakeSplitDegree production native.dim limit node
  let first := holPartition degreePredicate native.spill_wl
  have degreePartition : stExPartition (splitDegree native.dim limit)
      native.spill_wl [] [] native = (.success first, native) :=
    statePartition_pure _ _ _ _ degreePredicate native
      (fun node _ => splitDegree_production limit node related good)
  have actualFirst : partitionReversed
      (fun node => cakeSplitDegree production production.dim limit node)
      production.spillWl = first := by
    rw [related.dimension, related.spill, partitionReversed_production]
  have lowBounds : ∀ node ∈ first.1, node < native.dim := by
    intro node member
    have membership := (mem_holPart degreePredicate native.spill_wl [] [] node).1 member
    rcases membership with member | member
    · exact good.2.2.2.2.2.2.2.2.2.1 node member
    · cases member
  obtain ⟨revived, revival, represented⟩ := reviveMoves_production first.1 related good lowBounds
  let actualRevived := cakeReviveMoves first.1 production
  obtain ⟨shapeState, shapeRun, shape, _, _⟩ := reviveMovesSuccess native first.1 (by
    intro node member
    simpa only [good.1] using lowBounds node member)
  have same : shapeState = revived := congrArg Prod.snd (shapeRun.symm.trans revival)
  subst shapeState
  have moveLength : revived.move_related.length = native.move_related.length := by rw [shape]
  let movePredicate := fun node => cakeMoveRelatedSub actualRevived node
  let second := holPartition movePredicate first.1
  have moveReads : ∀ node ∈ first.1,
      moveRelatedSub node revived = (.success (movePredicate node), revived) := by
    intro node member
    have bound : node < revived.move_related.length := by
      rw [moveLength, good.2.2.2.2.1]
      exact lowBounds node member
    have value := represented.moveRelated_read node bound
    simp [moveRelatedSubEqn, bound, holEl_eq_getElem node revived.move_related bound,
      movePredicate, cakeMoveRelatedSub, actualRevived, value]
  have movePartition : stExPartition moveRelatedSub first.1 [] [] revived =
      (.success second, revived) := statePartition_pure _ _ _ _ movePredicate revived moveReads
  let result : State := {revived with
    spill_wl := first.2
    simp_wl := second.2 ++ revived.simp_wl
    freeze_wl := second.1 ++ revived.freeze_wl}
  have source : unspill limit native = (.success (), result) := by
    simp only [unspill, Translator.Monadic.MonadBase.bind, getDim, getSpillWl,
      degreePartition, ignoreBind, revival, movePartition,
      setSpillWl, addSimpWl, getSimpWl, setSimpWl, addFreezeWl, getFreezeWl, setFreezeWl]
    rfl
  have actual : cakeUnspill limit production = {actualRevived with
      spillWl := first.2
      simpWl := second.2 ++ actualRevived.simpWl
      freezeWl := second.1 ++ actualRevived.freezeWl} := by
    unfold cakeUnspill
    rw [actualFirst]
    simp only [partitionReversed_production, cakeAddSimpWl, cakeAddFreezeWl]
    rfl
  refine ⟨result, source, ?_⟩
  rw [actual]
  exact {represented with
    spill := rfl
    simplify := congrArg (second.2 ++ ·) represented.simplify
    freeze := congrArg (second.1 ++ ·) represented.freeze}

end Flapjack.RegAlloc
