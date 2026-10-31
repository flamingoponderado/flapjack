import Flapjack.Compiler.Backend.BviTmc.Proofs.ResultRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.MutableBlockRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.ListExtraction

/-! Source-shaped cases of the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.EvaluateRewrite
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- The empty-list case of the original TMC evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_rewrite_tmc"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap, wrapMap, workMap])]
theorem evaluate_rewrite_tmc_nil {C F : Type} (n : Nat × Nat)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [] env1 source = (result, final)) (_measure : n = (source.clock, 0))
    (_environments : envRel opt f env1 env2) (_safe : ∀ x ∈ ([] : List Bvi.Exp), noMutcons x)
    (states : stateRel f source target) (optLength : opt = true → ([] : List Bvi.Exp).length = 1)
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (@holHd Bvi.Exp ⟨.var 0⟩ []) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (@holHd Bvi.Exp ⟨.var 0⟩ []) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 target = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue')) := by
  simp [BviSem.evaluate] at run
  obtain ⟨rfl, rfl⟩ := run.symm
  refine ⟨target, f, .val [], ?_, ?_, states, ?_, onlyFresh_refl f target.refs,
    holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs, ?_⟩
  · simp [BviSem.evaluate]
  · simp [resultRel]
  · intro key value found; exact found
  · intro locOpt code
    constructor
    · intro wrap impossible
      simp at impossible
    · intro optTrue
      have impossible := optLength optTrue
      simp at impossible

end Flapjack.Compiler.Backend.BviTmc.EvaluateRewrite
