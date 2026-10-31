import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockLeaf
import Flapjack.Compiler.Backend.BviTmc.Proofs.IfWorker

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

/-- Flapjack infrastructure: the same allocated hole can be identified by
any in-bounds environment slot that contains its pointer. -/
theorem alloc_hole_reindex (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (extras extras' : List Value)
    (i i' idx ptr : Nat) (child : Value)
    (hole : CallBlockEnvironment.allocHoleHasVal f refs extras i idx child)
    (pointer : holEl i extras = .refPtr false ptr)
    (bound' : i' < extras'.length) (pointer' : holEl i' extras' = .refPtr false ptr) :
    CallBlockEnvironment.allocHoleHasVal f refs extras' i' idx child := by
  obtain ⟨holePtr, tag, left, right, _, holePointer, index, small, outside, found⟩ := hole
  rw [pointer] at holePointer
  have same : holePtr = ptr := by simpa using holePointer.symm
  subst holePtr
  exact ⟨ptr, tag, left, right, bound', pointer', index, small, outside, found⟩

/-- Flapjack infrastructure: an arbitrary auxiliary pointer slot supplies the
worker body with its trailing pointer and index arguments. -/
theorem aux_hole_to_worker_general (f : HolFiniteMapExact Nat Nat)
    (sourceArgs targetArgs extras : List Value) (slot ptr idx : Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (child : Value)
    (sameLength : sourceArgs.length = targetArgs.length)
    (hole : CallBlockEnvironment.allocHoleHasVal f refs extras slot idx child)
    (pointer : holEl slot extras = .refPtr false ptr) :
    holeHasVal f sourceArgs (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) refs child ∧
      holeNotFinalised refs ptr := by
  have single := alloc_hole_reindex f refs extras [.refPtr false ptr] slot 0 idx ptr child
    hole pointer (by simp) (by simp [holEl, holHd])
  exact aux_hole_to_worker f sourceArgs targetArgs ptr idx refs child sameLength single

/-- Flapjack infrastructure: a worker body returns its filled hole to the
same arbitrary auxiliary pointer slot. -/
theorem worker_hole_to_aux_general (f : HolFiniteMapExact Nat Nat)
    (sourceArgs targetArgs extras : List Value) (slot ptr idx : Nat)
    (refs : HolFiniteMapExact Nat (Ref Value)) (child : Value)
    (sameLength : sourceArgs.length = targetArgs.length)
    (hole : holeHasVal f sourceArgs (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) refs child)
    (notFinal : holeNotFinalised refs ptr) (bound : slot < extras.length)
    (pointer : holEl slot extras = .refPtr false ptr) :
    CallBlockEnvironment.allocHoleHasVal f refs extras slot idx child := by
  have single := worker_hole_to_aux f sourceArgs targetArgs ptr idx refs child sameLength hole notFinal
  exact alloc_hole_reindex f refs [.refPtr false ptr] extras 0 slot idx ptr child
    single (by simp [holEl, holHd]) bound pointer

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

/-- Flapjack infrastructure: an optimized result cannot return from the
callee if its source result cannot return. -/
theorem opt_result_no_return (f : HolFiniteMapExact Nat Nat) (source target : BviResult)
    (related : ResultRelation.optResRel f source target)
    (sourceNoReturn : ∀ values, source ≠ .err (.raise (.ret values))) :
    ∀ values, target ≠ .err (.raise (.ret values)) := by
  intro values eq
  subst target
  cases source with
  | val _ => simp [ResultRelation.optResRel] at related
  | err error =>
    cases error with
    | abort _ => simp [ResultRelation.optResRel, SemanticPrimitivesProps.excRel] at related
    | raise payload =>
      cases payload with
      | exn _ => simp [ResultRelation.optResRel, SemanticPrimitivesProps.excRel, ResultRelation.eorRel] at related
      | ret values' => exact sourceNoReturn values' rfl

/-- Flapjack infrastructure: the recursive-call auxiliary conclusion follows
from the smaller-clock worker-body simulation. Argument evaluation and lookup
are stated separately so this also covers shifted auxiliary environments. -/
theorem evaluate_aux_call_from_worker {C F : Type} (ticks dest : Nat) (indices : List Nat)
    (ptrExp idxExp : Bvi.Exp) (env sourceArgs targetArgs extras : List Value)
    (slot ptr idx : Nat) (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (oldRefs : HolFiniteMapExact Nat (Ref Value)) (body : Bvi.Exp)
    (sourceResult : BviResult) (sourceFinal : BviState (Nat × C) F) (initial : Value)
    (sameLength : sourceArgs.length = targetArgs.length)
    (domain : oldRefs.domain ⊆ target.refs.domain)
    (hole : CallBlockEnvironment.allocHoleHasVal f target.refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr)
    (argsRun : evaluate (indices.map Bvi.Exp.var) env target = (.val targetArgs, target))
    (ptrRun : evaluate [ptrExp] env target = (.val [.refPtr false ptr], target))
    (idxRun : evaluate [idxExp] env target = (.val [.number (Int.ofNat idx)], target))
    (found : findCode (some dest) (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) target.code =
      some (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)], body))
    (enough : ¬target.clock < ticks + 1)
    (sourceNoReturn : ∀ values, sourceResult ≠ .err (.raise (.ret values)))
    (worker : IfWorker.WorkerCore body sourceArgs
      (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) f
      (decClock (ticks + 1) target) ptr sourceResult sourceFinal) :
    ∃ result next g, evaluate [optimiseCallSource ticks dest indices ptrExp idxExp] env target = (result, next) ∧
      ResultRelation.optResRel g sourceResult result ∧ stateRel g sourceFinal next ∧
      finiteSubmap f g ∧ onlyFresh f g target.refs ∧
      holesUnchangedExcept f target.refs next.refs {ptr} ∧ holesStillNotFinalised f target.refs next.refs ∧
      ∀ sourceValue, sourceResult = .val [sourceValue] →
        ∃ targetValue, mutableBlockRel g oldRefs (next.refs.eraseEq ptr) sourceValue targetValue ∧
          CallBlockEnvironment.allocHoleHasVal f next.refs extras slot idx targetValue := by
  obtain ⟨result, g, next, run, resultRel, states, extension, fresh, unchanged, still, success⟩ := worker
  have noReturn := opt_result_no_return g sourceResult result resultRel sourceNoReturn
  have callRun := evaluate_optimise_call ticks dest indices ptrExp idxExp env target next targetArgs
    (.refPtr false ptr) (.number (Int.ofNat idx)) body result argsRun ptrRun idxRun found enough run noReturn
  have initialHole := aux_hole_to_worker_general f sourceArgs targetArgs extras slot ptr idx target.refs initial
    sameLength hole pointer
  have outside : ptr ∉ mapRange f := by
    obtain ⟨_, holePtr, _, _, _, _, ptrEq, _, _, out, _⟩ := initialHole.1
    have known : holEl sourceArgs.length (targetArgs ++ [.refPtr false ptr, .number (Int.ofNat idx)]) =
        .refPtr false ptr := by
      rw [holEl_eq_getElem _ _ (by simp [sameLength])]
      simp [List.getElem_append_right, sameLength]
    rw [known] at ptrEq
    have eq : holePtr = ptr := by simpa using ptrEq.symm
    simpa [eq] using out
  have bound : slot < extras.length := by obtain ⟨_, _, _, _, bound, _⟩ := hole; exact bound
  refine ⟨result, next, g, callRun, resultRel, states, extension, fresh, unchanged, still, ?_⟩
  intro sourceValue resultEq
  obtain ⟨targetValue, blocks, hole'⟩ := success sourceValue resultEq
  have finalNotFinal : holeNotFinalised next.refs ptr := still ptr outside initialHole.2
  exact ⟨targetValue,
    MutableBlockOld.mutableBlockRel_old_subset g target.refs (next.refs.eraseEq ptr) sourceValue targetValue oldRefs blocks domain,
    worker_hole_to_aux_general f sourceArgs targetArgs extras slot ptr idx next.refs targetValue
      sameLength hole' finalNotFinal bound pointer⟩

end Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerLeaf
