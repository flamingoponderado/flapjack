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

/-- Flapjack infrastructure: the recursive auxiliary call evaluates shifted
ordinary arguments, the selected hole pointer, and the constant hole index;
the resulting worker arguments satisfy the optimized environment relation. -/
theorem evaluate_aux_arguments {C F : Type} (indices : List Nat) (opt : Bool)
    (f : HolFiniteMapExact Nat Nat) (env1 env2 extras : List Value) (slot ptr idx : Nat)
    (state : BviState C F) (child : Value)
    (related : envRel opt f env1 env2) (wf : wfVars env1.length indices)
    (hole : CallBlockEnvironment.allocHoleHasVal f state.refs extras slot idx child)
    (pointer : holEl slot extras = .refPtr false ptr) :
    evaluate ((shiftVars extras.length indices).map Bvi.Exp.var) (extras ++ env2) state =
        (.val (indices.map (fun n => holEl n env2)), state) ∧
      evaluate [.var slot] (extras ++ env2) state = (.val [.refPtr false ptr], state) ∧
      evaluate [.op (.intOp (.const (Int.ofNat idx))) []] (extras ++ env2) state =
        (.val [.number (Int.ofNat idx)], state) ∧
      envRel true f (indices.map (fun n => holEl n env1))
        (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)]) := by
  obtain ⟨_, _, left, _, bound, _, index, small, _, _⟩ := hole
  have smallIdx : BackendCommon.smallEnoughInt (Int.ofNat idx) := by simpa [index] using small
  have fullBound : slot < (extras ++ env2).length := by simp; omega
  have slotEq : (extras ++ env2)[slot] = .refPtr false ptr := by
    simpa [List.getElem_append_left, bound, holEl_eq_getElem slot extras bound] using pointer
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [evaluate_shift_vars]
    exact evaluate_vars_target indices env1.length env2 state wf (envRel_length opt f env1 env2 related)
  · have run := evaluate_vars_target [slot] (extras ++ env2).length (extras ++ env2) state
      (by intro n member; simp only [List.mem_singleton] at member; subst n; exact fullBound) (Nat.le_refl _)
    simpa [holEl_eq_getElem slot (extras ++ env2) fullBound, slotEq] using run
  · rw [BviSem.evaluate, BviSem.fixClock_evaluate]
    simp only [BviSem.evaluate, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux]
    simp only [BackendCommon.smallEnoughInt] at smallIdx ⊢
    split <;> simp_all
  · exact CallBlockEnvironment.wfVars_env_rel_opt indices opt f env1 env2 ptr (Int.ofNat idx) related wf smallIdx

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

/-- Flapjack infrastructure: a resolved optimized call with an exhausted
clock times out before entering the worker body. -/
theorem evaluate_optimise_call_timeout {C F : Type} (ticks dest : Nat) (indices : List Nat)
    (ptr idx : Bvi.Exp) (env : List Value) (state : BviState C F)
    (values : List Value) (pointer index : Value) (body : Bvi.Exp)
    (argsRun : evaluate (indices.map Bvi.Exp.var) env state = (.val values, state))
    (ptrRun : evaluate [ptr] env state = (.val [pointer], state))
    (idxRun : evaluate [idx] env state = (.val [index], state))
    (found : findCode (some dest) (values ++ [pointer, index]) state.code =
      some (values ++ [pointer, index], body))
    (timeout : state.clock < ticks + 1) :
    evaluate [optimiseCallSource ticks dest indices ptr idx] env state =
      (.err (.abort .timeoutError), { state with clock := 0 }) := by
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
  simp [found, timeout]

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

/-- Flapjack infrastructure: the non-timeout auxiliary recursive-call case,
with argument evaluation and worker lookup derived from the original
environment, code relation and allocated-hole assumptions. The body
simulation is the remaining smaller-clock induction hypothesis. -/
theorem evaluate_aux_rcall_from_body {C F : Type} (loc workerLoc ticks : Nat) (indices : List Nat)
    (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 extras : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (slot ptr idx : Nat) (oldRefs : HolFiniteMapExact Nat (Ref Value)) (initial : Value)
    (body : Bvi.Exp) (sourceResult : BviResult) (sourceFinal : BviState (Nat × C) F)
    (environments : envRel opt f env1 env2) (wf : wfVars env1.length indices)
    (hole : CallBlockEnvironment.allocHoleHasVal f target.refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr) (domain : oldRefs.domain ⊆ target.refs.domain)
    (sourceFound : findCode (some loc) (indices.map (fun n => holEl n env1)) source.code =
      some (indices.map (fun n => holEl n env1), body))
    (code : optimisedCode loc workerLoc source.code target.code)
    (enough : ¬target.clock < ticks + 1)
    (sourceNoReturn : ∀ values, sourceResult ≠ .err (.raise (.ret values)))
    (bodyIH : ∀ worker,
      rewriteWorkerSource loc workerLoc indices.length (indices.length + 1) indices.length body = worker →
      envRel true f (indices.map (fun n => holEl n env1))
        (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)]) →
      holeHasVal f (indices.map (fun n => holEl n env1))
        (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)]) target.refs initial →
      holeNotFinalised target.refs ptr →
      IfWorker.WorkerCore worker (indices.map (fun n => holEl n env1))
        (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)])
        f (decClock (ticks + 1) target) ptr sourceResult sourceFinal) :
    ∃ result next g,
      evaluate [workerAuxSource (shiftBlock extras.length (.rCall ticks indices)) workerLoc slot idx]
        (extras ++ env2) target = (result, next) ∧
      ResultRelation.optResRel g sourceResult result ∧ stateRel g sourceFinal next ∧
      finiteSubmap f g ∧ onlyFresh f g target.refs ∧
      holesUnchangedExcept f target.refs next.refs {ptr} ∧ holesStillNotFinalised f target.refs next.refs ∧
      ∀ sourceValue, sourceResult = .val [sourceValue] →
        ∃ targetValue, mutableBlockRel g oldRefs (next.refs.eraseEq ptr) sourceValue targetValue ∧
          CallBlockEnvironment.allocHoleHasVal f next.refs extras slot idx targetValue := by
  obtain ⟨argsRun, ptrRun, idxRun, envRel'⟩ :=
    evaluate_aux_arguments indices opt f env1 env2 extras slot ptr idx target initial environments wf hole pointer
  have sameLength : (indices.map (fun n => holEl n env1)).length =
      (indices.map (fun n => holEl n env2)).length := by simp
  obtain ⟨worker, found, rewrite⟩ := find_worker_code loc workerLoc source.code target.code
    (indices.map (fun n => holEl n env1)) (indices.map (fun n => holEl n env2))
    (.refPtr false ptr) (.number (Int.ofNat idx)) body sourceFound sameLength code
  have hole' := aux_hole_to_worker_general f (indices.map (fun n => holEl n env1))
    (indices.map (fun n => holEl n env2)) extras slot ptr idx target.refs initial sameLength hole pointer
  have workerRun := bodyIH worker (by simpa using rewrite) envRel' hole'.1 hole'.2
  have simulation := evaluate_aux_call_from_worker ticks workerLoc (shiftVars extras.length indices)
    (.var slot) (.op (.intOp (.const (Int.ofNat idx))) []) (extras ++ env2)
    (indices.map (fun n => holEl n env1)) (indices.map (fun n => holEl n env2)) extras
    slot ptr idx f target oldRefs worker sourceResult sourceFinal initial sameLength domain hole pointer
    argsRun ptrRun idxRun found enough sourceNoReturn workerRun
  simpa [shiftBlock, workerAuxSource] using simulation

/-- Flapjack infrastructure: the auxiliary recursive-call timeout case
preserves the state and hole relations without entering the worker body. -/
theorem evaluate_aux_rcall_timeout {C F : Type} (loc workerLoc ticks : Nat) (indices : List Nat)
    (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 extras : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (slot ptr idx : Nat) (initial : Value) (body : Bvi.Exp)
    (environments : envRel opt f env1 env2) (wf : wfVars env1.length indices)
    (states : stateRel f source target)
    (hole : CallBlockEnvironment.allocHoleHasVal f target.refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr)
    (sourceFound : findCode (some loc) (indices.map (fun n => holEl n env1)) source.code =
      some (indices.map (fun n => holEl n env1), body))
    (code : optimisedCode loc workerLoc source.code target.code)
    (timeout : source.clock < ticks + 1) :
    evaluate [workerAuxSource (shiftBlock extras.length (.rCall ticks indices)) workerLoc slot idx]
        (extras ++ env2) target = (.err (.abort .timeoutError), { target with clock := 0 }) ∧
      stateRel f { source with clock := 0 } { target with clock := 0 } ∧
      onlyFresh f f target.refs ∧ holesUnchangedExcept f target.refs target.refs {ptr} ∧
      holesStillNotFinalised f target.refs target.refs := by
  obtain ⟨argsRun, ptrRun, idxRun, _⟩ :=
    evaluate_aux_arguments indices opt f env1 env2 extras slot ptr idx target initial environments wf hole pointer
  have sameLength : (indices.map (fun n => holEl n env1)).length =
      (indices.map (fun n => holEl n env2)).length := by simp
  obtain ⟨worker, found, _⟩ := find_worker_code loc workerLoc source.code target.code
    (indices.map (fun n => holEl n env1)) (indices.map (fun n => holEl n env2))
    (.refPtr false ptr) (.number (Int.ofNat idx)) body sourceFound sameLength code
  have targetTimeout : target.clock < ticks + 1 := by simpa [states.2.1] using timeout
  have run := evaluate_optimise_call_timeout ticks workerLoc (shiftVars extras.length indices)
    (.var slot) (.op (.intOp (.const (Int.ofNat idx))) []) (extras ++ env2) target
    (indices.map (fun n => holEl n env2)) (.refPtr false ptr) (.number (Int.ofNat idx)) worker
    argsRun ptrRun idxRun found targetTimeout
  exact ⟨by simpa [shiftBlock, workerAuxSource] using run, stateRel_with_clock 0 f source target states,
    onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs {ptr}, holesStill_refl f target.refs⟩

end Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerLeaf
