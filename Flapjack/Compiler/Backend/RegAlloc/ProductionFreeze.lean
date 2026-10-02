import Flapjack.Compiler.Backend.RegAlloc.ProductionSimplify

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- The whole actual freeze phase returns the native Boolean and represents
every final state field. Both branches and intermediate invariants are derived
from the original good state. This is cross-implementation infrastructure,
not a duplicate HOL do_freeze_success port; other allocator phases and native
initializer correspondence remain separate obligations. -/
theorem doFreeze_production (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result : State,
      doFreeze limit native = (.success (cakeDoFreeze limit production).1, result) ∧
      ProductionStateRel result (cakeDoFreeze limit production).2 := by
  cases freeze : native.freeze_wl with
  | nil =>
    have actualEmpty : production.freezeWl = [] := related.freeze.trans freeze
    refine ⟨native, ?_, ?_⟩
    · simp [doFreeze, Translator.Monadic.MonadBase.bind, getFreezeWl, freeze, ret,
        cakeDoFreeze, actualEmpty]
    · simpa [cakeDoFreeze, actualEmpty] using related
  | cons node rest =>
    have bound : node < native.dim :=
      good.2.2.2.2.2.2.2.2.2.2.1 node (by simp [freeze])
    obtain ⟨degrees, degreeRun, degreeLength, degreeRel⟩ :=
      decDegree_foreach_production [node] related good
    have singleton : stExForeach [node] decDegree native = decDegree node native := by
      simp only [stExForeach, ignoreBind, ret]
      cases decDegree node native with
      | mk result final =>
        cases result with
        | success payload => cases payload; rfl
        | failure error => rfl
    rw [singleton] at degreeRun
    have degreeRelated : ProductionStateRel {native with degrees := degrees}
        (cakeDecDegree node production) := by
      simpa only [List.foldl_cons, List.foldl_nil] using degreeRel
    have goodDegrees : goodRaState {native with degrees := degrees} := by
      obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
      exact ⟨a,b,degreeLength.trans c,d,e,f,g,h,i,j,k,l,m,n⟩
    let pushed : State := {native with
      degrees := degrees.set node 0
      move_related := native.move_related.set node false
      stack := node :: native.stack}
    have degreeBound : node < degrees.length := by rw [degreeLength, good.2.2.1]; exact bound
    have moveBound : node < native.move_related.length := by rwa [good.2.2.2.2.1]
    have pushRun : pushStack node {native with degrees := degrees} = (.success (), pushed) := by
      simp only [pushStack, Translator.Monadic.MonadBase.bind, getStack, ignoreBind,
        updateDegreesEqn, if_pos degreeBound, updateMoveRelatedEqn, if_pos moveBound, setStack]
      rfl
    have pushRelated := pushStack_production node degreeRelated goodDegrees bound
    rw [pushRun] at pushRelated
    simp only [ProductionLatchedUnitRel] at pushRelated
    have goodPush : goodRaState pushed := by
      obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := goodDegrees
      exact ⟨a,b,List.length_set.trans c,d,List.length_set.trans e,f,g,h,i,j,k,l,m,n⟩
    let afterFreeze : State := {pushed with freeze_wl := rest}
    let actualPush := cakePushStack node (cakeDecDegree node production)
    have goodTail : goodRaState afterFreeze := by
      obtain ⟨a,b,c,d,e,f,g,h,i,j,_,l,m,n⟩ := goodPush
      refine ⟨a,b,c,d,e,f,g,h,i,j,?_,l,m,n⟩
      intro next member
      exact good.2.2.2.2.2.2.2.2.2.2.1 next (by rw [freeze]; exact List.mem_cons_of_mem node member)
    have tailRelated : ProductionStateRel afterFreeze {actualPush with freezeWl := rest} :=
      {pushRelated with freeze := rfl}
    obtain ⟨result, unspillRun, finalRel⟩ := unspill_production limit tailRelated goodTail
    have actual : cakeDoFreeze limit production =
        (true, cakeUnspill limit {actualPush with freezeWl := rest}) := by
      simp only [cakeDoFreeze, related.freeze, freeze]
      rfl
    refine ⟨result, ?_, ?_⟩
    · rw [actual]
      simp only [doFreeze, Translator.Monadic.MonadBase.bind, getFreezeWl]
      rw [freeze]
      simp only [
        ignoreBind, degreeRun, pushRun, setFreezeWl]
      change ignoreBind (unspill limit) (ret true) afterFreeze = _
      simp only [ignoreBind, unspillRun, ret]
    · simpa only [actual] using finalRel

end Flapjack.RegAlloc
