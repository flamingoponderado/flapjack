import Flapjack.Compiler.Backend.BviTmc.Proofs.FillHole

/-! The raise case of the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.RaiseSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: the raise induction step with a specialized body
induction hypothesis. The original measure and redundant safety premises are
omitted; the body hypothesis supplies the ordinary, non-optimized simulation. -/
theorem evaluate_raise {C F : Type} (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.raise body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (ih : ∀ childResult childFinal,
      evaluate [body] env1 source = (childResult, childFinal) →
      childResult ≠ .err (.abort .typeError) →
      ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
        evaluate [body] env2 target = (nextResult, next) ∧
        resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) childResult nextResult ∧
        stateRel nextMap childFinal next ∧ finiteSubmap f nextMap ∧
        onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
        holesStillNotFinalised f target.refs next.refs) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [.raise body] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([.raise body] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (.raise body) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (.raise body) = work ∧
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
      (targetRun : evaluate [.raise body] env2 target = (.err targetError, next))
      (related : excRel (eorRel nextMap) sourceError targetError)
      (states : stateRel nextMap final next) (extension : finiteSubmap f nextMap)
      (fresh : onlyFresh f nextMap target.refs)
      (unchanged : holesUnchangedExcept f target.refs next.refs ∅)
      (still : holesStillNotFinalised f target.refs next.refs) :
      ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
        evaluate [.raise body] env2 target = (nextResult, next) ∧
        resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
        stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
        onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
        holesStillNotFinalised f target.refs next.refs ∧
        (∀ locOpt, optimisedCode loc locOpt source.code target.code →
          (∀ wrap, ([.raise body] : List Bvi.Exp).length = 1 ∧
              rewriteWrapperSource loc locOpt env1.length (.raise body) = some wrap →
            ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
              evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
              resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
              stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
              onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
              holesStillNotFinalised f target.refs wrapState.refs) ∧
          (opt = true → ∀ i j holePtr work,
            i = env1.length ∧ j = env1.length + 1 ∧
            (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
            rewriteWorkerSource loc locOpt i j env1.length (.raise body) = work ∧
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
      refine ⟨.err targetError, nextMap, next, targetRun, related, states, extension, fresh,
        holesUnchanged_subset f target.refs next.refs ∅ {holePtr} unchanged (by simp), still, ?_⟩
      intro _ impossible; cases impossible
  cases childRun : evaluate [body] env1 source with
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
      obtain ⟨value, rfl⟩ := evaluate_singleton body env1 source childFinal values childRun
      cases nextResult with
      | err error => simp [resultRel] at related
      | val values' =>
        obtain ⟨value', rfl⟩ := evaluate_singleton body env2 target next values' targetRun
        have valueRelated : valueRel nextMap value value' := by
          simp only [resultRel] at related
          cases related with
          | cons h _ => exact h
        have eq : (.err (.raise (.exn value)), childFinal) = (result, final) := by
          rw [BviSem.evaluate, childRun] at run
          exact run
        cases eq
        apply finish (.raise (.exn value)) (.raise (.exn value')) next nextMap rfl _
          valueRelated states extension fresh unchanged still
        rw [BviSem.evaluate, targetRun]
        rfl

end Flapjack.Compiler.Backend.BviTmc.RaiseSimulation
