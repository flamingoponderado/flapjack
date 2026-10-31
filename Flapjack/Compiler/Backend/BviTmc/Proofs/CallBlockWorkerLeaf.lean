import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockLeaf

/-! Evaluation of the recursive-call leaf of an optimized call block. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerLeaf
open BviTmc BviSem BvlSem

/-- Flapjack infrastructure: a source recursive call and its optimized-code
relation resolve the extended arguments to the corresponding worker body. -/
theorem find_worker_code (loc workerLoc : Nat) (sourceCode targetCode : Spt (Nat × Bvi.Exp))
    (sourceArgs targetArgs : List Value) (pointer index : Value) (body : Bvi.Exp)
    (found : findCode (some loc) sourceArgs sourceCode = some (sourceArgs, body))
    (sameLength : sourceArgs.length = targetArgs.length)
    (code : optimisedCode loc workerLoc sourceCode targetCode) :
    ∃ worker, findCode (some workerLoc) (targetArgs ++ [pointer, index]) targetCode =
      some (targetArgs ++ [pointer, index], worker) ∧
      rewriteWorkerSource loc workerLoc sourceArgs.length (sourceArgs.length + 1)
        sourceArgs.length body = worker := by
  obtain ⟨arity, original, wrapper, worker, sourceLookup, _, workerLookup, _, workerRewrite⟩ := code
  simp [findCode, sourceLookup] at found
  obtain ⟨length, bodyEq⟩ := found
  subst original
  refine ⟨worker, ?_, ?_⟩
  · simp [findCode, workerLookup, ← sameLength, length]
  · simpa [length] using workerRewrite

/-- Flapjack infrastructure: a worker's two trailing arguments identify the
same allocated, unfinalised hole in the auxiliary call-block environment. -/
theorem worker_hole_to_aux (f : HolFiniteMapExact Nat Nat)
    (sourceArgs targetArgs : List Value) (ptr idx : Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (child : Value)
    (sameLength : sourceArgs.length = targetArgs.length)
    (hole : holeHasVal f sourceArgs (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) refs child)
    (notFinal : holeNotFinalised refs ptr) :
    CallBlockEnvironment.allocHoleHasVal f refs [.refPtr false ptr] 0 idx child := by
  obtain ⟨_, holePtr, tag, finalised, left, right, ptrEq, idxEq, small, outside, found⟩ := hole
  have knownPtr : holEl sourceArgs.length (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) =
      .refPtr false ptr := by
    rw [holEl_eq_getElem _ _ (by simp [sameLength])]
    simp [List.getElem_append_right, sameLength]
  have knownIdx : holEl (sourceArgs.length + 1)
      (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) = .number (Int.ofNat idx) := by
    rw [holEl_eq_getElem _ _ (by simp [sameLength])]
    simp [List.getElem_append_right, sameLength]
  rw [knownPtr] at ptrEq
  have ptrSame : holePtr = ptr := by simpa using ptrEq.symm
  subst holePtr
  rw [knownIdx] at idxEq
  have idxSame : idx = left.length := by
    have equal : Int.ofNat idx = Int.ofNat left.length := by injection idxEq
    exact Int.ofNat_inj.mp equal
  obtain ⟨tag', left', child', right', unfinalised⟩ := notFinal
  rw [found] at unfinalised
  cases unfinalised
  exact ⟨ptr, tag, left, right, by simp, by simp [holEl, holHd], idxSame, small, outside, found⟩

/-- Flapjack infrastructure: an auxiliary hole provides the trailing pointer
and index expected by the optimized worker's function-body induction. -/
theorem aux_hole_to_worker (f : HolFiniteMapExact Nat Nat)
    (sourceArgs targetArgs : List Value) (ptr idx : Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (child : Value)
    (sameLength : sourceArgs.length = targetArgs.length)
    (hole : CallBlockEnvironment.allocHoleHasVal f refs [.refPtr false ptr] 0 idx child) :
    holeHasVal f sourceArgs (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) refs child ∧
      holeNotFinalised refs ptr := by
  obtain ⟨holePtr, tag, left, right, _, ptrEq, idxEq, small, outside, found⟩ := hole
  have same : holePtr = ptr := by simpa [holEl, holHd] using ptrEq.symm
  subst holePtr
  have knownPtr : holEl sourceArgs.length (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) =
      .refPtr false ptr := by
    rw [holEl_eq_getElem _ _ (by simp [sameLength])]
    simp [List.getElem_append_right, sameLength]
  have knownIdx : holEl (sourceArgs.length + 1)
      (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) = .number (Int.ofNat idx) := by
    rw [holEl_eq_getElem _ _ (by simp [sameLength])]
    simp [List.getElem_append_right, sameLength]
  refine ⟨⟨by simp [sameLength], ptr, tag, false, left, right, knownPtr, ?_, small, outside, found⟩,
    ⟨tag, left, child, right, found⟩⟩
  simpa [idxEq] using knownIdx

/-- Flapjack infrastructure: a worker call evaluates its ordinary arguments,
then the hole pointer and index, and executes the resolved worker body. The
worker simulation must still establish the body result and heap relations. -/
theorem evaluate_optimise_call {C F : Type} (ticks dest : Nat) (indices : List Nat)
    (ptr idx : Bvi.Exp) (env : List Value) (state next : BviState C F)
    (values : List Value) (pointer index : Value) (body : Bvi.Exp) (result : BviResult)
    (argsRun : evaluate (indices.map Bvi.Exp.var) env state = (.val values, state))
    (ptrRun : evaluate [ptr] env state = (.val [pointer], state))
    (idxRun : evaluate [idx] env state = (.val [index], state))
    (found : findCode (some dest) (values ++ [pointer, index]) state.code =
      some (values ++ [pointer, index], body))
    (enough : ¬state.clock < ticks + 1)
    (bodyRun : evaluate [body] (values ++ [pointer, index]) (decClock (ticks + 1) state) = (result, next))
    (noReturn : ∀ values, result ≠ .err (.raise (.ret values))) :
    evaluate [optimiseCallSource ticks dest indices ptr idx] env state = (result, next) := by
  have tailRun : evaluate [ptr, idx] env state = (.val [pointer, index], state) := by
    change evaluateTuple ([ptr] ++ [idx], env, state) = _
    rw [evaluateAppend]
    simp [BviSem.evaluateTuple, ptrRun, idxRun]
  have allRun : evaluate (indices.map Bvi.Exp.var ++ [ptr, idx]) env state =
      (.val (values ++ [pointer, index]), state) := by
    change evaluateTuple (_, env, state) = _
    rw [evaluateAppend]
    simp [BviSem.evaluateTuple, argsRun, tailRun]
  simp only [optimiseCallSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, allRun]
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, enough]
  rw [BviSem.fixClock_evaluate, bodyRun]
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | abort reason => rfl
    | raise payload =>
      cases payload with
      | exn value => rfl
      | ret values => exact False.elim (noReturn values rfl)

end Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerLeaf
