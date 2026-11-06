import Flapjack.Compiler.Backend.BviTmc.Proofs.FillHole

/-! TMC simulation for variable expressions. -/
namespace Flapjack.Compiler.Backend.BviTmc.VariableSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: this variable simulation omits the induction
measure and the automatically true singleton safety and length premises.
It is untagged because the original theorem includes those premises. -/
theorem evaluate_variable {C F : Type} (index : Nat)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.var index] env1 source = (result, final))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [.var index] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([.var index] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (.var index) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (.var index) = work ∧
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
  have sourceBound : index < env1.length := by
    by_contra invalid
    have failure : evaluate [.var index] env1 source = (.err (.abort .typeError), source) := by
      simp [BviSem.evaluate, invalid]
    rw [run] at failure
    exact notTypeError (congrArg Prod.fst failure)
  have targetBound : index < env2.length := by
    have length := envRel_length opt f env1 env2 environments
    omega
  have related := envRel_el opt f env1 env2 index environments sourceBound
  have sourceRun : evaluate [.var index] env1 source = (.val [holEl index env1], source) := by
    simp [BviSem.evaluate, sourceBound, holEl_eq_getElem index env1 sourceBound]
  have targetRun : evaluate [.var index] env2 target = (.val [holEl index env2], target) := by
    simp [BviSem.evaluate, targetBound, holEl_eq_getElem index env2 targetBound]
  have same := run.symm.trans sourceRun
  cases same
  refine ⟨target, f, .val [holEl index env2], targetRun, ?_, states, ?_,
    onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅,
    holesStill_refl f target.refs, ?_⟩
  · exact List.Forall₂.cons related .nil
  · intro key value found; exact found
  · intro locOpt _code
    constructor
    · intro wrap ⟨_, wrapper⟩
      simp [rewriteWrapperSource] at wrapper
    · intro optTrue i j holePtr work ⟨iEq, jEq, ⟨c, hole⟩, notFinal, worker, pointer⟩
      subst i
      subst j
      simp only [rewriteWorkerSource] at worker
      subst work
      have optEnvironments : envRel true f env1 env2 := by simpa [optTrue] using environments
      obtain ⟨workResult, workMap, workState, workRun, workRelation, workStates, extension, only,
        unchanged, still, fillValue, mutable, filledHole⟩ :=
        FillHole.evaluate_fill_hole_val (.var index) f f env1 env2 source source target target
          (holEl index env1) (holEl index env2) c holePtr sourceRun targetRun optEnvironments states
          (fun _ _ found => found) related hole notFinal (holesUnchanged_refl f target.refs ∅)
          (holesStill_refl f target.refs) (onlyFresh_refl f target.refs) states pointer
      refine ⟨workResult, workMap, workState, workRun, workRelation, workStates, extension, only,
        unchanged, still, ?_⟩
      intro resValue eq
      cases eq
      exact ⟨fillValue, mutable, filledHole⟩

end Flapjack.Compiler.Backend.BviTmc.VariableSimulation
