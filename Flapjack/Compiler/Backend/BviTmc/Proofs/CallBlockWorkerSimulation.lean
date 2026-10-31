import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockWorkerFrame

/-! Optimized worker simulation for recursive-call leaves. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerSimulation
open BviTmc BviSem BvlSem CallBlockWorkerFrame CallBlockWorkerLeaf CallBlockAuxSimulation

/-- Flapjack infrastructure: the non-timeout worker call follows from the
smaller-clock body simulation, retaining the original worker hole. -/
theorem evaluate_worker_rcall_body {C F : Type} (loc dest ticks ptr : Nat) (indices : List Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (f : HolFiniteMapExact Nat Nat) (initial : Value) (body : Bvi.Exp)
    (result : BviResult) (final : BviState (Nat × C) F)
    (environments : envRel true f env1 env2) (wf : wfVars env1.length indices)
    (states : stateRel f source target) (hole : holeHasVal f env1 env2 target.refs initial)
    (notFinal : holeNotFinalised target.refs ptr) (pointer : holEl env1.length env2 = .refPtr false ptr)
    (code : optimisedCode loc dest source.code target.code)
    (found : findCode (some loc) (indices.map (fun n => holEl n env1)) source.code =
      some (indices.map (fun n => holEl n env1), body))
    (bodyRun : evaluate [body] (indices.map (fun n => holEl n env1)) (decClock (ticks + 1) source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons body)
    (enough : ¬target.clock < ticks + 1) (noReturn : ∀ values, result ≠ .err (.raise (.ret values)))
    (bodyIH : WorkerBodyIH loc dest source env1 env2 f) :
    IfWorker.WorkerCore (workerBlockSource (.rCall ticks indices) dest env1.length (env1.length + 1))
      env1 env2 f target ptr result final := by
  obtain ⟨idx, allocHole, index⟩ := worker_hole_as_alloc f env1 env2 target.refs ptr initial hole notFinal pointer
  have small : BackendCommon.smallEnoughInt (Int.ofNat idx) := by
    obtain ⟨_, _, left, _, _, _, idxEq, small, _, _⟩ := allocHole
    simpa [idxEq] using small
  have sourceLength : (indices.map (fun n => holEl n env1)).length =
      (indices.map (fun n => holEl n env2)).length := by simp
  obtain ⟨worker, workerFound, rewrite⟩ := find_worker_code loc dest source.code target.code
    (indices.map (fun n => holEl n env1)) (indices.map (fun n => holEl n env2))
    (.refPtr false ptr) (.number (Int.ofNat idx)) body found sourceLength code
  have envRelated := CallBlockEnvironment.wfVars_env_rel_opt indices true f env1 env2 ptr (Int.ofNat idx)
    environments wf small
  have workerHole := aux_hole_to_worker_general f (indices.map (fun n => holEl n env1))
    (indices.map (fun n => holEl n env2)) env2 env1.length ptr idx target.refs initial sourceLength allocHole pointer
  have clockBound : ticks + 1 ≤ source.clock := by rw [← states.2.1]; omega
  have workerRun := bodyIH ticks indices target ptr idx initial body worker result final wf clockBound states code found bodyRun
    notTypeError safe (by simpa using rewrite) envRelated workerHole.1 workerHole.2
  have argsRun := evaluate_vars_target indices env1.length env2 target wf (envRel_length true f env1 env2 environments)
  have ptrBound : env1.length < env2.length := by have h := hole.1; omega
  have idxBound : env1.length + 1 < env2.length := by have h := hole.1; omega
  have ptrAt : env2[env1.length]? = some (.refPtr false ptr) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨ptrBound, by simpa [holEl_eq_getElem env1.length env2 ptrBound] using pointer⟩
  have idxAt : env2[env1.length + 1]? = some (.number (Int.ofNat idx)) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨idxBound, by simpa [holEl_eq_getElem (env1.length + 1) env2 idxBound] using index⟩
  have ptrRun : evaluate [.var env1.length] env2 target = (.val [.refPtr false ptr], target) := by
    simp [BviSem.evaluate, ptrAt]
  have idxRun : evaluate [.var (env1.length + 1)] env2 target = (.val [.number (Int.ofNat idx)], target) := by
    simp [BviSem.evaluate, idxAt]
  obtain ⟨targetResult, next, g, targetRun, related, nextStates, extension, fresh, unchanged, still, success⟩ :=
    evaluate_aux_call_from_worker ticks dest indices (.var env1.length) (.var (env1.length + 1)) env2
      (indices.map (fun n => holEl n env1)) (indices.map (fun n => holEl n env2)) env2 env1.length ptr idx f target
      target.refs _ result final initial sourceLength (Set.Subset.rfl) allocHole pointer argsRun ptrRun idxRun
      workerFound enough noReturn workerRun
  refine ⟨targetResult, g, next, ?_, related, nextStates, extension, fresh, unchanged, still, ?_⟩
  · simpa [workerBlockSource] using targetRun
  · intro value eq
    obtain ⟨targetValue, blocks, returnedHole⟩ := success value eq
    exact ⟨targetValue, blocks, alloc_hole_as_worker f env1 env2 next.refs ptr idx targetValue
      hole.1 pointer index returnedHole⟩

/-- Flapjack infrastructure: optimized worker simulation of a source
recursive call, including timeout and the smaller-clock body case. -/
theorem evaluate_worker_rcall {C F : Type} (loc dest ticks ptr : Nat) (indices : List Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (f : HolFiniteMapExact Nat Nat) (initial : Value) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [callBlockToBvi loc (.rCall ticks indices)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel true f env1 env2)
    (wf : wfVars env1.length indices) (states : stateRel f source target)
    (hole : holeHasVal f env1 env2 target.refs initial) (notFinal : holeNotFinalised target.refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr)
    (code : optimisedCode loc dest source.code target.code) (bodyIH : WorkerBodyIH loc dest source env1 env2 f) :
    IfWorker.WorkerCore (workerBlockSource (.rCall ticks indices) dest env1.length (env1.length + 1))
      env1 env2 f target ptr result final := by
  have sourceArgs := evaluate_vars_source indices env1 source wf
  obtain ⟨arity, body, wrapper, worker, sourceLookup, targetLookup, workerLookup, wrapRewrite, workerRewrite⟩ := code
  have code' : optimisedCode loc dest source.code target.code :=
    ⟨arity, body, wrapper, worker, sourceLookup, targetLookup, workerLookup, wrapRewrite, workerRewrite⟩
  simp only [callBlockToBvi] at run
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, sourceArgs] at run
  by_cases arityEq : (indices.map (fun n => holEl n env1)).length = arity
  · have found : findCode (some loc) (indices.map (fun n => holEl n env1)) source.code =
        some (indices.map (fun n => holEl n env1), body) := by simp [findCode, sourceLookup, arityEq]
    have safe : noMutcons body := (findCode_rel f _ _ source target (some loc) _ body found
      (CallBlockEnvironment.wfVars_list_rel indices true f env1 env2 environments wf) states).1
    by_cases timeout : source.clock < ticks + 1
    · obtain ⟨idx, _, index⟩ := worker_hole_as_alloc f env1 env2 target.refs ptr initial hole notFinal pointer
      have ptrBound : env1.length < env2.length := by have h := hole.1; omega
      have idxBound : env1.length + 1 < env2.length := by have h := hole.1; omega
      have ptrAt : env2[env1.length]? = some (.refPtr false ptr) := by
        apply List.getElem?_eq_some_iff.mpr
        exact ⟨ptrBound, by simpa [holEl_eq_getElem env1.length env2 ptrBound] using pointer⟩
      have idxAt : env2[env1.length + 1]? = some (.number (Int.ofNat idx)) := by
        apply List.getElem?_eq_some_iff.mpr
        exact ⟨idxBound, by simpa [holEl_eq_getElem (env1.length + 1) env2 idxBound] using index⟩
      have ptrRun : evaluate [.var env1.length] env2 target = (.val [.refPtr false ptr], target) := by
        simp [BviSem.evaluate, ptrAt]
      have idxRun : evaluate [.var (env1.length + 1)] env2 target = (.val [.number (Int.ofNat idx)], target) := by
        simp [BviSem.evaluate, idxAt]
      have argsRun := evaluate_vars_target indices env1.length env2 target wf (envRel_length true f env1 env2 environments)
      have sameLength : (indices.map (fun n => holEl n env1)).length =
          (indices.map (fun n => holEl n env2)).length := by simp
      obtain ⟨workerBody, workerFound, _⟩ := find_worker_code loc dest source.code target.code
        (indices.map (fun n => holEl n env1)) (indices.map (fun n => holEl n env2))
        (.refPtr false ptr) (.number (Int.ofNat idx)) body found sameLength code'
      have targetTimeout : target.clock < ticks + 1 := by simpa [states.2.1] using timeout
      have targetRun := evaluate_optimise_call_timeout ticks dest indices (.var env1.length) (.var (env1.length + 1))
        env2 target (indices.map (fun n => holEl n env2)) (.refPtr false ptr) (.number (Int.ofNat idx)) workerBody
        argsRun ptrRun idxRun workerFound targetTimeout
      simp [found, timeout] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      refine ⟨.err (.abort .timeoutError), f, { target with clock := 0 }, ?_, ?_,
        stateRel_with_clock 0 f source target states, ?_, onlyFresh_refl f target.refs,
        holesUnchanged_refl f target.refs {ptr}, holesStill_refl f target.refs, ?_⟩
      · simpa [workerBlockSource] using targetRun
      · rfl
      · intro key value h; exact h
      · intro _ impossible; cases impossible
    · have targetEnough : ¬target.clock < ticks + 1 := by simpa [states.2.1] using timeout
      simp only [found, timeout, ↓reduceIte] at run
      rw [BviSem.fixClock_evaluate] at run
      cases bodyRun : evaluate [body] (indices.map (fun n => holEl n env1))
          (decClock (ticks + 1) source) with
      | mk bodyResult bodyFinal =>
        simp only [bodyRun] at run
        have bodyPair : (bodyResult, bodyFinal) = (result, final) := by
          cases bodyResult with
          | val values => simpa [bodyRun] using run
          | err error =>
            cases error with
            | abort reason => simpa [bodyRun] using run
            | raise payload =>
              cases payload with
              | exn value => simpa [bodyRun] using run
              | ret values =>
                simp at run
                exact False.elim (notTypeError run.1.symm)
        have noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values)) := by
          intro values bad
          rw [bad] at run
          simp at run
          exact notTypeError run.1.symm
        cases bodyPair
        exact evaluate_worker_rcall_body loc dest ticks ptr indices source target env1 env2 f initial body result final
          environments wf states hole notFinal pointer code' found bodyRun notTypeError safe targetEnough noReturn bodyIH
  · have arityNe : indices.length ≠ arity := by simpa using arityEq
    simp [findCode, sourceLookup, arityNe] at run
    exact False.elim (notTypeError run.1.symm)

/-- Flapjack infrastructure: optimized worker simulation for any well-formed
call block, assuming the smaller-clock function-body worker simulation. -/
theorem evaluate_worker_cb {C F : Type} (loc dest ptr : Nat) (cb : CallBlock)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (f : HolFiniteMapExact Nat Nat) (initial : Value) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [callBlockToBvi loc cb] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel true f env1 env2)
    (wf : wfBlock env1.length cb) (states : stateRel f source target)
    (hole : holeHasVal f env1 env2 target.refs initial) (notFinal : holeNotFinalised target.refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr)
    (code : optimisedCode loc dest source.code target.code) (bodyIH : WorkerBodyIH loc dest source env1 env2 f) :
    IfWorker.WorkerCore (workerBlockSource cb dest env1.length (env1.length + 1))
      env1 env2 f target ptr result final := by
  cases cb with
  | rCall ticks indices =>
    exact evaluate_worker_rcall loc dest ticks ptr indices source target env1 env2 f initial result final
      run notTypeError environments wf states hole notFinal pointer code bodyIH
  | callBlock tag left child right =>
    exact evaluate_worker_frame_core loc dest tag ptr left right child source target env1 env2 f initial result final
      run notTypeError environments states wf hole notFinal pointer code bodyIH

end Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerSimulation
