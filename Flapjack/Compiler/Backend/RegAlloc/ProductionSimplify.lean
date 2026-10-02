import Flapjack.Compiler.Backend.RegAlloc.ProductionUnspill
import Flapjack.Compiler.Backend.RegAlloc.ProductionStackTransition
import Flapjack.Compiler.Backend.RegAlloc.ProductionDegreeTraversal

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem degree_good {native : State} {degrees : List Nat}
    (good : goodRaState native) (length : degrees.length = native.degrees.length) :
    goodRaState {native with degrees := degrees} := by
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
  exact ⟨a,b,length.trans c,d,e,f,g,h,i,j,k,l,m,n⟩

private theorem unit_ignore_ret (operation : M State Unit StateException) (state : State) :
    ignoreBind operation (ret ()) state = operation state := by
  unfold ignoreBind ret
  cases operation state with
  | mk result final =>
    cases result with
    | success payload => cases payload; rfl
    | failure error => rfl

/-- Actual degree-neighbour traversal agrees with the complete native
FOREACH under its original good state invariant. Degree length, success, and
all final fields are derived. Flapjack correspondence infrastructure. -/
theorem decDegree_foreach_production (nodes : List Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) :
    ∃ degrees, stExForeach nodes decDegree native =
        (.success (), {native with degrees := degrees}) ∧
      degrees.length = native.degrees.length ∧
      ProductionStateRel {native with degrees := degrees}
        (nodes.foldl (fun state node => cakeDecDegree node state) production) := by
  induction nodes generalizing native production with
  | nil => exact ⟨native.degrees, rfl, rfl, related⟩
  | cons node rest ih =>
    obtain ⟨first, run, length⟩ := decDegreeSuccess [node] native good
    have source : decDegree node native = (.success (), {native with degrees := first}) := by
      simpa only [stExForeach, unit_ignore_ret] using run
    have represented := decDegree_production node related
    rw [source] at represented
    simp only [ProductionLatchedUnitRel] at represented
    obtain ⟨degrees, tailRun, tailLength, tailRel⟩ := ih represented (degree_good good length)
    refine ⟨degrees, ?_, tailLength.trans length, tailRel⟩
    simpa only [stExForeach, ignoreBind, source] using tailRun

/-- The whole executed simplify phase has the native Boolean result and full
post-state relation, for both source branches. Degree traversal, pushes,
worklist clearing and unspill run in source order. Intermediate good states
are derived from reviewed native invariants, not supplied as extra premises.
This actual/native transport has no separate HOL original; it is not a second
port of do_simplify_success and does not close the other allocator phases. -/
theorem doSimplify_production (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result : State,
      doSimplify limit native = (.success (cakeDoSimplify limit production).1, result) ∧
      ProductionStateRel result (cakeDoSimplify limit production).2 := by
  by_cases empty : native.simp_wl = []
  · have actualEmpty : production.simpWl = [] := related.simplify.trans empty
    refine ⟨native, ?_, ?_⟩
    · simp [doSimplify, Translator.Monadic.MonadBase.bind, getSimpWl, empty, ret,
        cakeDoSimplify, actualEmpty]
    · simpa [cakeDoSimplify, actualEmpty] using related
  obtain ⟨degrees, degreeRun, degreeLength, degreeRel⟩ :=
    decDegree_foreach_production native.simp_wl related good
  let afterDegrees := native.simp_wl.foldl (fun state node => cakeDecDegree node state) production
  have goodDegrees := degree_good good degreeLength
  obtain ⟨pushed, pushRun, pushRel⟩ := pushStack_foreach_production native.simp_wl
    degreeRel goodDegrees good.2.2.2.2.2.2.2.2.1
  obtain ⟨finalDegrees, moves, stack, nativePush, finalLength, moveLength⟩ :=
    pushStackSuccess native.simp_wl {native with degrees := degrees}
      ⟨good.2.2.2.2.2.2.2.2.1, goodDegrees⟩
  have pushedShape : pushed = {native with
      degrees := finalDegrees
      move_related := moves
      stack := stack} := congrArg Prod.snd (pushRun.symm.trans nativePush)
  subst pushed
  let afterPush := native.simp_wl.foldl (fun state node => cakePushStack node state) afterDegrees
  have goodPush : goodRaState {native with
      degrees := finalDegrees
      move_related := moves
      stack := stack} := by
    obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := goodDegrees
    exact ⟨a,b,finalLength.trans c,d,moveLength.trans e,f,g,h,i,j,k,l,m,n⟩
  let cleared : State := {native with
    degrees := finalDegrees
    move_related := moves
    stack := stack
    simp_wl := []}
  have goodClear : goodRaState cleared := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m,n⟩ := goodPush
    exact ⟨a,b,c,d,e,f,g,h,fun _ member => False.elim (List.not_mem_nil member),j,k,l,m,n⟩
  have clearRel : ProductionStateRel cleared {afterPush with simpWl := []} :=
    {pushRel with simplify := rfl}
  obtain ⟨result, unspillRun, finalRel⟩ := unspill_production limit clearRel goodClear
  have actual : cakeDoSimplify limit production =
      (true, cakeUnspill limit {afterPush with simpWl := []}) := by
    have actualNonempty : production.simpWl ≠ [] := by rwa [related.simplify]
    unfold cakeDoSimplify
    split
    · contradiction
    · rw [related.simplify]
      change (true, cakeUnspill limit
        {afterDegrees.simpWl.foldl (fun state node => cakePushStack node state) afterDegrees
          with simpWl := []}) = _
      rw [degreeRel.simplify]
  refine ⟨result, ?_, ?_⟩
  · rw [actual]
    simp only [doSimplify, Translator.Monadic.MonadBase.bind, getSimpWl, if_neg empty,
      ignoreBind, degreeRun, nativePush, setSimpWl, ret]
    have finalRun : unspill limit {native with degrees := finalDegrees, move_related := moves, stack := stack, simp_wl := []} = (.success (), result) := unspillRun
    rw [finalRun]
  · simpa only [actual] using finalRel

end Flapjack.RegAlloc
