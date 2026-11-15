module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.Induction

@[expose] public section

/-! Complete call-block simulation for the TMC proof. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockCorrectness
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation
open CallBlockAuxFrame CallBlockAuxSimulation ClockHypothesis

/-- Source-shaped `evaluate_cb` from `bvi_tmcProofScript.sml`. This remains
untagged pending a reviewed representation qualifier for the body-universal map
in `Induction.hypothesis`. Evaluation inherits the rational-cuts real model
(SOUNDNESS item 8). -/
theorem evaluate_cb {C F A : Type} (cb : CallBlock) (loc : Nat)
    (f : HolFiniteMapExact Nat Nat) (opt : Bool) (env1 env2 : List Value)
    (source : BviState (Nat × C) F) (target : BviState C F)
    (final : BviState (Nat × C) F) (result : BviResult) (clock : Nat)
    (h : evaluate [callBlockToBvi loc cb] env1 source = (result, final) ∧
      wfBlock env1.length cb ∧ envRel opt f env1 env2 ∧ stateRel f source target ∧
      source.clock ≤ clock ∧ result ≠ .err (.abort .typeError) ∧
      (∀ xs (s : BviState (Nat × C) F), Induction.hypothesis xs s clock)) :
    (∃ (r : BviResult), ∃ (s : BviState C F), ∃ (ordinaryMap : HolFiniteMapExact Nat Nat),
      evaluate [callBlockToBvi loc cb] env2 target = (r, s) ∧
      resultRel (List.Forall₂ (valueRel ordinaryMap)) (eorRel ordinaryMap) result r ∧ stateRel ordinaryMap final s ∧
      f.submap ordinaryMap ∧ onlyFresh f ordinaryMap target.refs ∧ holesUnchangedExcept f target.refs s.refs ∅ ∧
      holesStillNotFinalised f target.refs s.refs) ∧
    ∀ dest, optimisedCode loc dest source.code target.code →
      (∀ tag left child right, cb = .callBlock tag left child right →
        ∃ (s : BviState C F), ∃ (wrapMap : HolFiniteMapExact Nat Nat), ∃ (r : BviResult),
          evaluate [wrapperBlockSource tag left child right dest] env2 target = (r, s) ∧
          resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result r ∧ stateRel wrapMap final s ∧
          f.submap wrapMap ∧ onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs s.refs ∅ ∧
          holesStillNotFinalised f target.refs s.refs) ∧
      (∀ (refs : HolFiniteMapExact Nat (Ref Value)) extras slot idx ptr,
        stateRefRel f source.refs refs ∧
        (∃ c, CallBlockEnvironment.allocHoleHasVal f refs extras slot idx c) ∧
        target.refs.domain ⊆ refs.domain ∧ holEl slot extras = .refPtr false ptr →
        ∃ (r : BviResult), ∃ (s : BviState C F), ∃ (auxMap : HolFiniteMapExact Nat Nat),
          evaluate [workerAuxSource (shiftBlock extras.length cb) dest slot idx] (extras ++ env2)
            { target with refs := refs } = (r, s) ∧
          optResRel auxMap result r ∧ stateRel auxMap final s ∧ f.submap auxMap ∧ onlyFresh f auxMap refs ∧
          holesUnchangedExcept f refs s.refs {ptr} ∧ holesStillNotFinalised f refs s.refs ∧
          ∀ v, result = .val [v] → ∃ v',
            mutableBlockRel auxMap target.refs (s.refs.eraseEq ptr) v v' ∧
            CallBlockEnvironment.allocHoleHasVal f s.refs extras slot idx v') ∧
      (opt = true → ∀ slot idx (_work : A) ptr,
        slot = env1.length ∧ idx = env1.length + 1 ∧
        (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs ptr ∧
        holEl slot env2 = .refPtr false ptr →
        ∃ (r : BviResult), ∃ (workMap : HolFiniteMapExact Nat Nat), ∃ (s : BviState C F),
          evaluate [workerBlockSource cb dest slot idx] env2 target = (r, s) ∧
          optResRel workMap result r ∧ stateRel workMap final s ∧ f.submap workMap ∧ onlyFresh f workMap target.refs ∧
          holesUnchangedExcept f target.refs s.refs {ptr} ∧ holesStillNotFinalised f target.refs s.refs ∧
          ∀ v, result = .val [v] → ∃ v', mutableBlockRel workMap target.refs (s.refs.eraseEq ptr) v v' ∧
            holeHasVal f env1 env2 s.refs v') := by
  obtain ⟨run, wf, env, states, _, noError, _⟩ := h
  have ih : SmallerClockIH (C := C) (F := F) source.clock := by
    intro e s t a b o g l r last less run safe env states noError
    exact (Induction.evaluate_general l [e] s t a b o g r last run noError
      (by simpa using safe) env states (by simp)).2 e rfl
  have ordinary := ordinary_body_from_smaller_clock loc source target env1 env2 f states ih
  obtain ⟨next, g, r, ordinaryPost⟩ :=
    CallBlockLeaf.evaluate_cb_ordinary loc cb source env1 opt f target env2 env states ordinary
      result final wf run noError
  refine ⟨⟨r, next, g, ordinaryPost⟩, ?_⟩
  intro dest code
  have worker := worker_body_from_smaller_clock loc dest source env1 env2 f ih
  refine ⟨?_, ?_, ?_⟩
  · intro tag left child right shape
    subst cb
    exact evaluate_wrapper_cb loc dest tag left right child source target env1 env2 opt f result final
      env states wf run noError code worker
  · intro refs extras slot idx ptr h
    obtain ⟨heap, ⟨initial, hole⟩, domain, pointer⟩ := h
    have newStates : stateRel f source ({ target with refs := refs } : BviState C F) := ⟨heap, states.2⟩
    exact evaluate_aux_cb loc dest cb source env1 env2 opt f target.refs env worker
      { target with refs := refs } extras slot idx ptr initial result final wf run noError
      newStates domain hole pointer code
  · intro optTrue slot idx work ptr h
    obtain ⟨rfl, rfl, ⟨initial, hole⟩, notFinal, pointer⟩ := h
    have trueEnv : envRel true f env1 env2 := by simpa [optTrue] using env
    exact CallBlockWorkerSimulation.evaluate_worker_cb loc dest ptr cb source target env1 env2 f initial
      result final run noError trueEnv wf states hole notFinal pointer code worker

end Flapjack.Compiler.Backend.BviTmc.CallBlockCorrectness
