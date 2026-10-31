import Flapjack.Compiler.Backend.BviTmc.Proofs.LetSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.IfWorker

/-! Optimized let simulation for an extracted call block. -/
namespace Flapjack.Compiler.Backend.BviTmc.LetWorkerBlock
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation IfWorker MutableBlockOld

/-- Flapjack infrastructure: simulate a let whose target body is a call-block
worker, using the binding and call-block induction hypotheses. -/
theorem evaluate_let_worker_block {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (cb : CallBlock)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc locOpt holePtr : Nat)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel true f env1 env2)
    (c : Value) (hole : holeHasVal f env1 env2 target.refs c)
    (notFinal : holeNotFinalised target.refs holePtr)
    (pointer : holEl env1.length env2 = .refPtr false holePtr)
    (code : optimisedCode loc locOpt source.code target.code)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      values.length = bindings.length →
      evaluate [body] (values ++ env1) mid = (result, final) →
      envRel true g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      holeHasVal g (values ++ env1) (values' ++ env2) t.refs c → holeNotFinalised t.refs holePtr →
      holEl (values ++ env1).length (values' ++ env2) = .refPtr false holePtr →
      optimisedCode loc locOpt mid.code t.code →
      WorkerCore (workerBlockSource cb locOpt (values ++ env1).length ((values ++ env1).length + 1))
        (values ++ env1) (values' ++ env2) g t holePtr result final) :
    WorkerCore (.let bindings (workerBlockSource cb locOpt (bindings.length + env1.length)
      (bindings.length + env1.length + 1))) env1 env2 f target holePtr result final := by
  have outside : holePtr ∉ mapRange f := by
    obtain ⟨_, ptr, _, _, _, _, ptrEq, _, _, out, _⟩ := hole
    rw [pointer] at ptrEq
    have same : ptr = holePtr := by simpa using ptrEq.symm
    simpa [same] using out
  cases bindingsRun : evaluate bindings env1 source with
  | mk bindingsResult middle =>
    have bindingsSafe : bindingsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingsResult
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
      exact notTypeError (congrArg Prod.fst run.symm)
    obtain ⟨middleTarget, g, targetResult, targetRun, related, middleStates, extension,
      fresh, unchanged, still⟩ := bindingsIH bindingsResult middle bindingsRun bindingsSafe
    cases bindingsResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err error' =>
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨.err error', g, middleTarget, ?_, related, middleStates, extension, fresh,
          holesUnchanged_subset f target.refs middleTarget.refs ∅ {holePtr} unchanged (by simp), still, ?_⟩
        · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
        · intro _ impossible; cases impossible
    | val values =>
      cases targetResult with
      | err error => simp [resultRel] at related
      | val values' =>
        have valuesRelated : List.Forall₂ (valueRel g) values values' := related
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
        have nextHole : holeHasVal g env1 env2 middleTarget.refs c := by
          obtain ⟨length, ptr, tag, finalised, left, right, ptrEq, idxEq, small, ptrOutside, found⟩ := hole
          obtain ⟨nextFinal, nextChild, nextFound, sameChild⟩ := unchanged ptr tag finalised left c right ptrOutside found
          have childEq : c = nextChild := sameChild (by simp)
          have allocated : ptr ∈ target.refs.domain := by simp [HolFiniteMapExact.domain, found]
          have nextOutside := nonFresh_not_in_range f g target.refs ptr allocated ptrOutside fresh
          exact ⟨length, ptr, tag, nextFinal, left, right, ptrEq, idxEq, small, nextOutside, by simpa [childEq] using nextFound⟩
        have nextNotFinal : holeNotFinalised middleTarget.refs holePtr := still holePtr outside notFinal
        have extendedHole := holeHasVal_append g env1 env2 middleTarget.refs c values values' nextHole valuesRelated
        have valueLength := evaluate_length bindings env1 source middle values bindingsRun
        have lengthEq := valuesRelated.length_eq
        have bound : env1.length < env2.length := by have := envRel_length_opt f env1 env2 environments; omega
        have extendedBound : (values ++ env1).length < (values' ++ env2).length := by
          simp only [List.length_append]; omega
        have extendedPointer : holEl (values ++ env1).length (values' ++ env2) = .refPtr false holePtr := by
          rw [holEl_eq_getElem _ _ bound] at pointer
          rw [holEl_eq_getElem _ _ extendedBound]
          simpa [List.length_append, lengthEq, List.getElem_append_right] using pointer
        have nextCode := WrapperCases.evaluate_pres_opt_code loc locOpt source middle target middleTarget
          bindings env1 env2 (.val values) (.val values') code bindingsRun targetRun
        obtain ⟨workResult, h, workState, workRun, workRel, states, bodyExtension,
          bodyFresh, bodyUnchanged, bodyStill, filled⟩ :=
          bodyIH values values' middle g middleTarget valueLength run
            (envRel_append true g env1 env2 values values' (envRel_submap true f g env1 env2 environments extension) valuesRelated)
            middleStates extendedHole nextNotFinal extendedPointer nextCode
        have submap : finiteSubmap f h := by
          intro k v found; exact bodyExtension k v (extension k v found)
        have domain := BviProps.evaluate_refs_subset bindings env2 target middleTarget (.val values') targetRun
        have allFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh bodyFresh domain
        have widened := holesUnchanged_subset f target.refs middleTarget.refs ∅ {holePtr} unchanged (by simp)
        have allUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs workState.refs {holePtr}
          widened bodyUnchanged fresh extension
        have allStill := holesStill_trans f g target.refs middleTarget.refs workState.refs ()
          still bodyStill fresh extension
        refine ⟨workResult, h, workState, ?_, workRel, states, submap, allFresh, allUnchanged, allStill, ?_⟩
        · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
          simpa [List.length_append, valueLength, Nat.add_comm, Nat.add_assoc] using workRun
        · intro resValue success
          obtain ⟨resValue', block, filledHole⟩ := filled resValue success
          have baseHole := holeHasVal_unappend g values values' env1 env2 workState.refs resValue' filledHole valuesRelated
          refine ⟨resValue', ?_, holeHasVal_submap f g env1 env2 workState.refs resValue' baseHole extension⟩
          exact mutableBlockRel_old_subset h middleTarget.refs (workState.refs.eraseEq holePtr)
            resValue resValue' target.refs block domain

end Flapjack.Compiler.Backend.BviTmc.LetWorkerBlock
