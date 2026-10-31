import Flapjack.Compiler.Backend.BviTmc.Proofs.FillHole

/-! The return case of the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.ReturnSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: the return induction step with a specialized argument-list
induction hypothesis. The original measure and redundant safety premises are
omitted; the argument-list hypothesis supplies the ordinary, non-optimized simulation. -/
theorem evaluate_return {C F : Type} (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.return args] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (ih : ∀ childResult childFinal,
      evaluate args env1 source = (childResult, childFinal) →
      childResult ≠ .err (.abort .typeError) →
      ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
        evaluate args env2 target = (nextResult, next) ∧
        resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) childResult nextResult ∧
        stateRel nextMap childFinal next ∧ finiteSubmap f nextMap ∧
        onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
        holesStillNotFinalised f target.refs next.refs) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [.return args] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([.return args] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (.return args) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (.return args) = work ∧
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
  have finish (sourceError targetError : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
      (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat)
      (sourceResult : result = .err sourceError)
      (targetRun : evaluate [.return args] env2 target = (.err targetError, next))
      (related : excRel (eorRel nextMap) sourceError targetError)
      (states : stateRel nextMap final next) (extension : finiteSubmap f nextMap)
      (fresh : onlyFresh f nextMap target.refs)
      (unchanged : holesUnchangedExcept f target.refs next.refs ∅)
      (still : holesStillNotFinalised f target.refs next.refs) :
      ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
        evaluate [.return args] env2 target = (nextResult, next) ∧
        resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
        stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
        onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
        holesStillNotFinalised f target.refs next.refs ∧
        (∀ locOpt, optimisedCode loc locOpt source.code target.code →
          (∀ wrap, ([.return args] : List Bvi.Exp).length = 1 ∧
              rewriteWrapperSource loc locOpt env1.length (.return args) = some wrap →
            ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
              evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
              resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
              stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
              onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
              holesStillNotFinalised f target.refs wrapState.refs) ∧
          (opt = true → ∀ i j holePtr work,
            i = env1.length ∧ j = env1.length + 1 ∧
            (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
            rewriteWorkerSource loc locOpt i j env1.length (.return args) = work ∧
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
    subst result
    refine ⟨next, nextMap, .err targetError, targetRun, related, states, extension, fresh,
      unchanged, still, ?_⟩
    intro locOpt _code
    constructor
    · intro wrap ⟨_, wrapper⟩
      simp [rewriteWrapperSource] at wrapper
    · intro _opt i j holePtr work ⟨_, _, _, _, worker, _⟩
      simp only [rewriteWorkerSource] at worker
      subst work
      have workRun := FillHole.evaluate_fillHole_error (.return args) i j env2 target next targetError targetRun
      refine ⟨.err targetError, nextMap, next, workRun, related, states, extension, fresh,
        holesUnchanged_subset f target.refs next.refs ∅ {holePtr} unchanged (by simp), still, ?_⟩
      intro _ impossible; cases impossible
  cases childRun : evaluate args env1 source with
  | mk childResult childFinal =>
    have childSafe : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [BviSem.evaluate, childRun] at run
      exact notTypeError run.1.symm
    obtain ⟨next, nextMap, nextResult, targetRun, related, states, extension, fresh,
      unchanged, still⟩ := ih childResult childFinal childRun childSafe
    cases childResult with
    | err error =>
      cases nextResult with
      | val values => simp [resultRel] at related
      | err error' =>
        have eq : (.err error, childFinal) = (result, final) := by
          simpa [BviSem.evaluate, childRun] using run
        cases eq
        apply finish error error' next nextMap rfl _ related states extension fresh unchanged still
        simp [BviSem.evaluate, targetRun]
    | val values =>
      cases nextResult with
      | err error => simp [resultRel] at related
      | val values' =>
        have eq : (.err (.raise (.ret values)), childFinal) = (result, final) := by
          simpa [BviSem.evaluate, childRun] using run
        cases eq
        apply finish (.raise (.ret values)) (.raise (.ret values')) next nextMap rfl _
          related states extension fresh unchanged still
        simp [BviSem.evaluate, targetRun]

end Flapjack.Compiler.Backend.BviTmc.ReturnSimulation
