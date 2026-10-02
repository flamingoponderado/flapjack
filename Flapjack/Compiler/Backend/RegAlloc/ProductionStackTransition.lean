import Flapjack.Compiler.Backend.RegAlloc.ProductionDegreeTransition
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- A bounded native stack push preserves all represented fields. This is
cross-implementation infrastructure, with no independent HOL declaration. -/
private theorem pushStack_bounded (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production)
    (degreeBound : node < native.degrees.length)
    (moveBound : node < native.move_related.length) :
    pushStack node native = (.success (),
      {native with
        degrees := native.degrees.set node 0
        move_related := native.move_related.set node false
        stack := node :: native.stack}) ∧
    ProductionStateRel
      {native with
        degrees := native.degrees.set node 0
        move_related := native.move_related.set node false
        stack := node :: native.stack}
      (cakePushStack node production) := by
  constructor
  · simp only [pushStack, Translator.Monadic.MonadBase.bind, getStack, ignoreBind,
      updateDegreesEqn, if_pos degreeBound, updateMoveRelatedEqn, if_pos moveBound,
      setStack]
  · have updated := (related.degree_write node 0 degreeBound).moveRelated_write
      node false moveBound
    exact { updated with stack := by simpa [cakePushStack] using congrArg (node :: ·) related.stack }

/-- The actual push agrees with the native transition on the original
push_stack_success invariant and node bound. Array bounds are derived from
that invariant. Malformed states outside these source premises remain a
separate phase-transport obligation; no total-error equivalence is claimed.
This correspondence theorem has no independent HOL original. -/
theorem pushStack_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    ProductionLatchedUnitRel (pushStack node native) (cakePushStack node production) := by
  have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
  have moveBound : node < native.move_related.length := by rwa [good.2.2.2.2.1]
  obtain ⟨source, result⟩ := pushStack_bounded node related degreeBound moveBound
  simpa only [source, ProductionLatchedUnitRel] using result

private theorem pushStack_foreach_bounded (nodes : List Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (bounds : ∀ node ∈ nodes,
      node < native.degrees.length ∧ node < native.move_related.length) :
    ∃ result : State, stExForeach nodes pushStack native = (.success (), result) ∧
      ProductionStateRel result (nodes.foldl (fun state node => cakePushStack node state) production) := by
  induction nodes generalizing native production with
  | nil => exact ⟨native, rfl, related⟩
  | cons node rest ih =>
    have bound := bounds node List.mem_cons_self
    obtain ⟨source, updated⟩ := pushStack_bounded node related bound.1 bound.2
    obtain ⟨result, run, represented⟩ := ih updated (by
      intro next member
      simpa using bounds next (List.mem_cons_of_mem node member))
    refine ⟨result, ?_, represented⟩
    simpa only [stExForeach, ignoreBind, source] using run

/-- Complete native FOREACH/actual fold stack-push correspondence under the
same invariant and EVERY-node bound used by HOL push_stack_success. Native
success and the entire final production state relation are proved, not taken
as premises. This is untagged cross-implementation infrastructure, not another
port of the already reviewed native success theorem. -/
theorem pushStack_foreach_production (nodes : List Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (bounds : ∀ node ∈ nodes, node < native.dim) :
    ∃ result : State, stExForeach nodes pushStack native = (.success (), result) ∧
      ProductionStateRel result (nodes.foldl (fun state node => cakePushStack node state) production) := by
  apply pushStack_foreach_bounded nodes related
  intro node member
  have bound := bounds node member
  constructor
  · rwa [good.2.2.1]
  · rwa [good.2.2.2.2.1]

end Flapjack.RegAlloc
