module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Callee
public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull
public import Flapjack.Compiler.Backend.Semantics.DataProps.Ticks
public import Flapjack.Misc.Sptree.UnionAlgebra

@[expose] public section

/-! The complete Call case of the BVI-to-data compiler simulation. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace CallCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end CallCarrier

/-- Call case of compiler correctness, using the guarded recursive induction
hypotheses from the BVI evaluator. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem simulationFor_call {C F : Type} (ticks : Nat) (dest : Option Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F)
    (argsIH : ¬(dest.isNone ∧ handler.isSome) → simulationFor args env s1)
    (calleeIH : ∀ values state callArgs body,
      ¬(dest.isNone ∧ handler.isSome) →
      BviSem.evaluate args env s1 = (.val values, state) →
      BvlSem.findCode dest values state.code = some (callArgs, body) →
      ¬(state.clock < ticks + 1) →
      simulationFor [body] callArgs (BviSem.decClock (ticks + 1) state))
    (handlerIH : ∀ values state callArgs body resultState value expression,
      ¬(dest.isNone ∧ handler.isSome) →
      BviSem.evaluate args env s1 = (.val values, state) →
      BvlSem.findCode dest values state.code = some (callArgs, body) →
      ¬(state.clock < ticks + 1) →
      BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) state) =
        (.err (.raise (.exn value)), resultState) →
      handler = some expression → simulationFor [expression] (value :: env) resultState) :
    simulationFor [.call ticks dest args handler] env s1 := by
  intro res s2 t1 n corr tail live run notType vars tailShape fresh related livePresent exceptionJump
  by_cases valid : ¬(dest.isNone ∧ handler.isSome)
  · generalize argsRun : BviSem.evaluate args env s1 = pair
    obtain ⟨argsResult, smid⟩ := pair
    cases argsResult with
    | err error =>
      rw [BviSem.evaluate] at run
      simp only [Bool.and_eq_true, if_neg valid] at run
      rw [BviSem.fixClock_evaluate, argsRun] at run
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨t2, first, pres, names, nmid, ls, compiled, target, finalRel, outcome⟩ :=
        argsIH valid (.err error) smid t1 n corr false live argsRun notType vars (by simp) fresh related livePresent exceptionJump
      cases pres with
      | none => simp [correctOutcome] at outcome
      | some result =>
        have sourceBound := BviSem.evaluate_clock_le args env s1
        rw [argsRun] at sourceBound
        have targetBound : t2.clock ≤ t1.clock := by
          simpa [← related.1, ← finalRel.1] using sourceBound
        cases handler with
        | none =>
          let ret := if tail then none else some ([nmid], namesOfList (live ++ corr))
          refine ⟨t2, .seq first (DataLang.mkTicks ticks (.call ret dest names none)), some result,
            [nmid], nmid + 1, ls, ?_, ?_, finalRel, ?_⟩
          · simp [compileSource, compiled, ret]
          · exact evaluateSeq_stop first _ t1 t2 result target targetBound
          · simpa [correctOutcome, isResult] using outcome
        | some handler =>
          generalize handlerCompiled : compileSource (nmid + 1) (nmid :: corr) false live [handler] = triple
          obtain ⟨handlerCode, handlerValues, n2⟩ := triple
          let ret := some ([n2], namesOfList (live ++ corr))
          let after := if tail then DataLang.Prog.return [n2] else .skip
          let rest := DataLang.mkTicks ticks (.seq (.call ret dest names
            (some (nmid, .seq handlerCode (.move n2 (Flapjack.holHd handlerValues))))) after)
          refine ⟨t2, .seq first rest, some result, [n2], n2 + 1, ls, ?_, ?_, finalRel, ?_⟩
          · simp [compileSource, compiled, handlerCompiled, ret, rest, after]
          · exact evaluateSeq_stop first _ t1 t2 result target targetBound
          · simpa [correctOutcome, isResult] using outcome
    | val values =>
      obtain ⟨tmid, first, pres, names, nmid, ls, compiled, target, middleRel, outcome⟩ :=
        argsIH valid (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
          (by simp [isException])
      cases pres with
      | some result => simp [correctOutcome, isResult] at outcome
      | none =>
        rw [BviSem.evaluate] at run
        simp only [Bool.and_eq_true, if_neg valid] at run
        rw [BviSem.fixClock_evaluate, argsRun] at run
        cases found : BvlSem.findCode dest values smid.code with
        | none =>
          simp [found, BviSem.typeError] at run
          exact False.elim (notType run.1.symm)
        | some pair =>
          obtain ⟨callArgs, body⟩ := pair
          by_cases clock : smid.clock < ticks + 1
          · have runTimeout : res = .err (.abort .timeoutError) ∧ s2 = { smid with clock := 0 } := by
              simpa [found, clock, BviSem.timeoutError] using run.symm
            obtain ⟨rfl, rfl⟩ := runTimeout
            have sourceBound := BviSem.evaluate_clock_le args env s1
            rw [argsRun] at sourceBound
            have targetBound : tmid.clock ≤ t1.clock := by
              simpa [← related.1, ← middleRel.1] using sourceBound
            by_cases early : smid.clock < ticks
            · have earlyTarget : tmid.clock < ticks := by simpa [← middleRel.1] using early
              let final := { tmid with clock := 0, locals := .ln, stack := [], localsSize := some 0 }
              cases handler with
              | none =>
                let ret := if tail then none else some ([nmid], namesOfList (live ++ corr))
                let call := DataLang.Prog.call ret dest names none
                refine ⟨final, .seq first (DataLang.mkTicks ticks call), some (.err (.abort .timeoutError)),
                  [nmid], nmid + 1, none, ?_, ?_, ?_, ?_⟩
                · simp [compileSource, compiled, ret, call]
                · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                  simp [DataSem.evaluate_mkTicks, earlyTarget, final]
                · simpa [stateRel, final] using middleRel.2
                · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
              | some handler =>
                generalize handlerCompiled : compileSource (nmid + 1) (nmid :: corr) false live [handler] = triple
                obtain ⟨handlerCode, handlerValues, n2⟩ := triple
                let ret := some ([n2], namesOfList (live ++ corr))
                let after := if tail then DataLang.Prog.return [n2] else .skip
                let inner := DataLang.Prog.seq (.call ret dest names
                  (some (nmid, .seq handlerCode (.move n2 (Flapjack.holHd handlerValues))))) after
                refine ⟨final, .seq first (DataLang.mkTicks ticks inner), some (.err (.abort .timeoutError)),
                  [n2], n2 + 1, none, ?_, ?_, ?_, ?_⟩
                · simp [compileSource, compiled, handlerCompiled, ret, inner, after]
                · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                  simp [DataSem.evaluate_mkTicks, earlyTarget, final]
                · simpa [stateRel, final] using middleRel.2
                · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
            · have sourceEq : smid.clock = ticks := by omega
              have targetEq : tmid.clock = ticks := by rw [← middleRel.1, sourceEq]
              have firstOutcome := outcome
              have liveMidAll := correctOutcome_live values t1 tmid n nmid corr live names env ls outcome livePresent
              have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
                intro v member
                exact liveMidAll v (List.mem_append_right names member)
              rcases outcome with ⟨_, _, _, _, envVars, _, _, _, _, _, resultVars⟩
              obtain ⟨dataValues, dataRead, projected⟩ := getVars_lift names values tmid.locals resultVars
              have foundProjected : BvlSem.findCode dest (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
                simpa [projected] using found
              obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
                findCode_projection dest dataValues smid tmid callArgs body middleRel foundProjected
              have rootsPresent : ∀ key ∈ live ++ corr, sptLookup key tmid.locals ≠ none := by
                simpa [DataSem.getVars] using
                  (roots_present tmid [] live corr env [] envVars liveMid (by simp [DataSem.getVars]))
              let saved := sptMkWf (sptInter tmid.locals (namesOfList (live ++ corr)))
              have cut : DataSem.cutEnv (namesOfList (live ++ corr)) tmid.locals = some saved :=
                cutEnv_namesOfList (live ++ corr) tmid.locals rootsPresent
              let timed := { tmid with clock := 0 }
              cases handler with
              | none =>
                cases tail with
                | true =>
                  let final := DataSem.flushState true timed
                  refine ⟨final, .seq first (DataLang.mkTicks ticks (.call none dest names none)),
                    some (.err (.abort .timeoutError)), [nmid], nmid + 1, none, ?_, ?_, ?_, ?_⟩
                  · simp [compileSource, compiled]
                  · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                    simp [DataSem.evaluate_mkTicks, targetEq, timed, DataSem.evaluate, dataRead, targetCode, final]
                  · simpa [stateRel, final, DataSem.flushState, timed] using middleRel.2
                  · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
                | false =>
                  let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock timed))
                  let final := { entered with stack := [], locals := .ln }
                  refine ⟨final, .seq first (DataLang.mkTicks ticks
                    (.call (some ([nmid], namesOfList (live ++ corr))) dest names none)),
                    some (.err (.abort .timeoutError)), [nmid], nmid + 1, none, ?_, ?_, ?_, ?_⟩
                  · simp [compileSource, compiled]
                  · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                    simp [DataSem.evaluate_mkTicks, targetEq, timed, DataSem.evaluate, dataRead, targetCode,
                      cut, entered, final]
                  · simpa [stateRel, final, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using middleRel.2
                  · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
              | some handler =>
                generalize handlerCompiled : compileSource (nmid + 1) (nmid :: corr) false live [handler] = triple
                obtain ⟨handlerCode, handlerValues, n2⟩ := triple
                let ret := some ([n2], namesOfList (live ++ corr))
                let after := if tail then DataLang.Prog.return [n2] else .skip
                let inner := DataLang.Prog.seq (.call ret dest names
                  (some (nmid, .seq handlerCode (.move n2 (Flapjack.holHd handlerValues))))) after
                let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved true (DataSem.decClock timed))
                let final := { entered with stack := [], locals := .ln }
                refine ⟨final, .seq first (DataLang.mkTicks ticks inner), some (.err (.abort .timeoutError)),
                  [n2], n2 + 1, none, ?_, ?_, ?_, ?_⟩
                · simp [compileSource, compiled, handlerCompiled, ret, inner, after]
                · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                  simp [DataSem.evaluate_mkTicks, targetEq, timed, inner, DataSem.evaluate,
                    DataSem.fixClock, dataRead, targetCode, cut, ret, entered, final,
                    DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
                · simpa [stateRel, final, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using middleRel.2
                · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
          · have firstOutcome := outcome
            have liveMidAll := correctOutcome_live values t1 tmid n nmid corr live names env ls outcome livePresent
            have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
              intro v member
              exact liveMidAll v (List.mem_append_right names member)
            rcases outcome with ⟨_, _, _, freshMid, envVars, _, _, _, _, jumpMid, resultVars⟩
            obtain ⟨dataValues, dataRead, projected⟩ := getVars_lift names values tmid.locals resultVars
            have foundProjected : BvlSem.findCode dest (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
              simpa [projected] using found
            obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
              findCode_projection dest dataValues smid tmid callArgs body middleRel foundProjected
            have rootsPresent : ∀ key ∈ live ++ corr, sptLookup key tmid.locals ≠ none := by
              simpa [DataSem.getVars] using
                (roots_present tmid [] live corr env [] envVars liveMid (by simp [DataSem.getVars]))
            let saved := sptMkWf (sptInter tmid.locals (namesOfList (live ++ corr)))
            have cut : DataSem.cutEnv (namesOfList (live ++ corr)) tmid.locals = some saved :=
              cutEnv_namesOfList (live ++ corr) tmid.locals rootsPresent
            let timed := { tmid with clock := tmid.clock - ticks }
            have timedNonzero : timed.clock ≠ 0 := by
              have h := middleRel.1
              simp only [timed]
              omega
            have entryRel : stateRel (BviSem.decClock (ticks + 1) smid)
                (DataSem.callEnv dataArgs size (DataSem.decClock timed)) := by
              rcases middleRel with ⟨clockRel, remaining⟩
              constructor
              · simp [BviSem.decClock, DataSem.callEnv, DataSem.decClock, timed, ← clockRel, Nat.sub_add_eq]
              · simpa [BviSem.decClock, DataSem.callEnv, DataSem.decClock, timed] using remaining
            have recursive := calleeIH values smid callArgs body valid argsRun found clock
            cases handler with
            | none =>
              simp only [found, if_neg clock] at run
              rw [BviSem.fixClock_evaluate] at run
              have calleeFacts : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (res, s2) ∧ ¬isReturn res := by
                cases callRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) with
                | mk result next =>
                  cases result with
                  | val values =>
                    simp [callRun] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact ⟨rfl, by simp [isReturn]⟩
                  | err error =>
                    cases error with
                    | abort reason =>
                      simp [callRun] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact ⟨rfl, by simp [isReturn]⟩
                    | raise raised =>
                      cases raised with
                      | exn value =>
                        simp [callRun] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact ⟨rfl, by simp [isReturn]⟩
                      | ret values =>
                        simp [callRun, BviSem.typeError] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact False.elim (notType rfl)
              subst callArgs
              cases tail with
              | true =>
                let entered := DataSem.callEnv dataArgs size (DataSem.decClock timed)
                have entryLocals : entered.locals = sptFromList dataArgs := rfl
                have entryJump : isException res → DataSem.jumpExc entered ≠ none := by
                  intro raised
                  have available := jumpMid (exceptionJump raised)
                  cases oldJump : DataSem.jumpExc tmid with
                  | none => exact False.elim (available oldJump)
                  | some jumped =>
                    have transported := DataSem.jumpExc_transport tmid entered jumped rfl rfl oldJump
                    rw [transported]
                    simp
                obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                  compileCalleeFull body dataArgs (BviSem.decClock (ticks + 1) smid) s2 entered res
                    recursive calleeFacts.1 notType entryRel entryLocals entryJump
                have projectedResult := calleeOutcome.1 calleeFacts.2
                have callOutcome : correctOutcome res tmid targetNext nmid (nmid + 1) corr live [nmid] env true (some result) ls2 := by
                  refine ⟨fun _ => projectedResult, fun returned => False.elim (calleeFacts.2 returned), ?_, by simp, ?_⟩
                  · intro resultOrReturn
                    simpa [entered, DataSem.callEnv, DataSem.decClock, timed] using calleeOutcome.2.2.1 resultOrReturn
                  · intro raised
                    simpa [entered, DataSem.callEnv, DataSem.decClock, timed] using calleeOutcome.2.2.2.2 raised
                have sourceBound := BviSem.evaluate_clock_le args env s1
                rw [argsRun] at sourceBound
                have targetBound : tmid.clock ≤ t1.clock := by
                  simpa [← related.1, ← middleRel.1] using sourceBound
                have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                refine ⟨targetNext, .seq first (DataLang.mkTicks ticks (.call none dest names none)),
                  some result, [nmid], nmid + 1, ls2, ?_, ?_, finalRel, ?_⟩
                · simp [compileSource, compiled]
                · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                  have run' : DataSem.evaluate (compileExp dataArgs.length body)
                      (DataSem.callEnv dataArgs size (DataSem.decClock timed)) = (some result, targetNext) := targetRun
                  rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                  change DataSem.evaluate (.call none dest names none) timed = _
                  have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                  have codeTimed : DataSem.findCode dest dataValues timed.code timed.stackFrameSizes =
                      some (dataArgs, compileExp dataArgs.length body, size) := by simpa [timed] using targetCode
                  simp [DataSem.evaluate, readTimed, codeTimed, timedNonzero, run']
                · exact correctOutcome_seq values res t1 tmid targetNext n nmid (nmid + 1) corr live names [nmid]
                    env true (some result) ls ls2 firstOutcome callOutcome
              | false =>
                let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock timed))
                have entryRel' : stateRel (BviSem.decClock (ticks + 1) smid) entered := by
                  simpa [stateRel, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using entryRel
                have entryLocals : entered.locals = sptFromList dataArgs := rfl
                have entryJump : isException res → DataSem.jumpExc entered ≠ none := by
                  intro raised
                  have original := jumpMid (exceptionJump raised)
                  change DataSem.jumpExc (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock timed))) ≠ none
                  rw [DataSem.jumpExc_callEnv_push_noHandler]
                  cases jumpRun : DataSem.jumpExc tmid with
                  | none => exact False.elim (original jumpRun)
                  | some jumped =>
                    have transported := DataSem.jumpExc_transport tmid timed jumped rfl rfl jumpRun
                    rw [transported]
                    simp
                obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                  compileCalleeFull body dataArgs (BviSem.decClock (ticks + 1) smid) s2 entered res
                    recursive calleeFacts.1 notType entryRel' entryLocals entryJump
                have projectedResult := calleeOutcome.1 calleeFacts.2
                have sourceBound := BviSem.evaluate_clock_le args env s1
                rw [argsRun] at sourceBound
                have targetBound : tmid.clock ≤ t1.clock := by
                  simpa [← related.1, ← middleRel.1] using sourceBound
                have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                have codeTimed : DataSem.findCode dest dataValues timed.code timed.stackFrameSizes =
                    some (dataArgs, compileExp dataArgs.length body, size) := by simpa [timed] using targetCode
                have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                cases result with
                | val returned =>
                  have resultEq : res = .val (returned.map dataToBviValue) := by
                    simpa [dataToBviResult] using projectedResult.symm
                  have singleton := BviSem.evaluate_singleton body (dataArgs.map dataToBviValue)
                    (BviSem.decClock (ticks + 1) smid) s2 (returned.map dataToBviValue) (by simpa [resultEq] using calleeFacts.1)
                  obtain ⟨sourceValue, singleton⟩ := singleton
                  have lengthOne : returned.length = 1 := by
                    have length := congrArg List.length singleton
                    simpa using length
                  cases returned with
                  | nil => simp at lengthOne
                  | cons dataResult rest =>
                    cases rest with
                    | cons other more => simp at lengthOne
                    | nil =>
                      have sourceResult : res = .val [dataToBviValue dataResult] := by
                        simpa [dataToBviResult] using projectedResult.symm
                      subst res
                      have sourceIsResult : isResult (.val [dataToBviValue dataResult]) := ⟨_, rfl⟩
                      obtain ⟨stack, handler⟩ := calleeOutcome.2.2.1 (Or.inl sourceIsResult)
                      have stackEq : targetNext.stack = .env tmid.localsSize saved :: tmid.stack := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using stack.symm
                      have handlerEq : targetNext.handler = tmid.handler := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using handler.symm
                      let restored := { targetNext with stack := tmid.stack, locals := saved, localsSize := tmid.localsSize }
                      have popRun : DataSem.popEnv targetNext = some restored := by
                        simp [DataSem.popEnv, stackEq, restored]
                      let final := DataSem.setVar nmid dataResult restored
                      have setSingleton : DataSem.setVars [nmid] [dataResult] restored = final := by
                        simp [DataSem.setVars, DataSem.setVar, sptFromAList, sptUnion_insert_ln, final]
                      have relFinal : stateRel s2 final := by
                        simpa [stateRel, final, restored, DataSem.setVar] using finalRel
                      have callOutcome := forceValueOutcome tmid final nmid corr live env dataResult envVars freshMid
                        (by rfl) (by rfl) (by simpa [final, restored, DataSem.setVar] using handlerEq)
                      refine ⟨final, .seq first (DataLang.mkTicks ticks
                        (.call (some ([nmid], namesOfList (live ++ corr))) dest names none)),
                        none, [nmid], nmid + 1, none, ?_, ?_, relFinal, ?_⟩
                      · simp [compileSource, compiled]
                      · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                        rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                        change DataSem.evaluate (.call (some ([nmid], namesOfList (live ++ corr))) dest names none) timed = _
                        have clamped : DataSem.fixClock entered ((some (.val [dataResult]) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                            ((some (.val [dataResult]) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                          rw [← targetRun, DataSem.fixClock_evaluate]
                        simp [DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun,
                          clamped, popRun, setSingleton]
                      · exact correctOutcome_seq values (.val [dataToBviValue dataResult]) t1 tmid final n nmid (nmid + 1)
                          corr live names [nmid] env false none ls none firstOutcome callOutcome
                | err error =>
                  cases error with
                  | abort reason =>
                    have sourceResult : res = .err (.abort reason) := by simpa [dataToBviResult] using projectedResult.symm
                    subst res
                    have callOutcome : correctOutcome (.err (.abort reason)) tmid targetNext nmid (nmid + 1) corr live [nmid] env false (some (.err (.abort reason))) ls2 := by
                      simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
                    refine ⟨targetNext, .seq first (DataLang.mkTicks ticks
                      (.call (some ([nmid], namesOfList (live ++ corr))) dest names none)),
                      some (.err (.abort reason)), [nmid], nmid + 1, ls2, ?_, ?_, finalRel, ?_⟩
                    · simp [compileSource, compiled]
                    · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                      rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                      change DataSem.evaluate (.call (some ([nmid], namesOfList (live ++ corr))) dest names none) timed = _
                      have clamped : DataSem.fixClock entered ((some (.err (.abort reason)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                          ((some (.err (.abort reason)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by rw [← targetRun, DataSem.fixClock_evaluate]
                      simp [DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun, clamped]
                    · exact correctOutcome_seq values (.err (.abort reason)) t1 tmid targetNext n nmid (nmid + 1)
                        corr live names [nmid] env false _ ls ls2 firstOutcome callOutcome
                  | raise raised =>
                    have sourceResult : res = .err (.raise (.exn (dataToBviValue raised))) := by
                      simpa [dataToBviResult] using projectedResult.symm
                    subst res
                    have raisedResult : isException (.err (.raise (.exn (dataToBviValue raised)))) := ⟨_, rfl⟩
                    have calleeJump := calleeOutcome.2.2.2.2 raisedResult
                    have jumpRun : DataSem.jumpExc { targetNext with stack := .env tmid.localsSize saved :: tmid.stack, handler := tmid.handler } =
                        some { targetNext with localsSize := ls2 } := by
                      simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using calleeJump
                    have stripped := jumpExc_stripSaved tmid targetNext saved ls2 (jumpMid (exceptionJump raisedResult)) jumpRun
                    have callOutcome : correctOutcome (.err (.raise (.exn (dataToBviValue raised)))) tmid targetNext nmid (nmid + 1) corr live [nmid] env false (some (.err (.raise raised))) ls2 := by
                      simp [correctOutcome, dataToBviResult, isReturn, isResult, isException, stripped]
                    refine ⟨targetNext, .seq first (DataLang.mkTicks ticks
                      (.call (some ([nmid], namesOfList (live ++ corr))) dest names none)),
                      some (.err (.raise raised)), [nmid], nmid + 1, ls2, ?_, ?_, finalRel, ?_⟩
                    · simp [compileSource, compiled]
                    · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                      rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                      change DataSem.evaluate (.call (some ([nmid], namesOfList (live ++ corr))) dest names none) timed = _
                      have clamped : DataSem.fixClock entered ((some (.err (.raise raised)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                          ((some (.err (.raise raised)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by rw [← targetRun, DataSem.fixClock_evaluate]
                      simp [DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun, clamped]
                    · exact correctOutcome_seq values (.err (.raise (.exn (dataToBviValue raised)))) t1 tmid targetNext n nmid (nmid + 1)
                        corr live names [nmid] env false _ ls ls2 firstOutcome callOutcome
            | some handler =>
              simp only [found, if_neg clock] at run
              rw [BviSem.fixClock_evaluate] at run
              subst callArgs
              let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved true (DataSem.decClock timed))
              have entryRel' : stateRel (BviSem.decClock (ticks + 1) smid) entered := by
                simpa [stateRel, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using entryRel
              have entryLocals : entered.locals = sptFromList dataArgs := rfl
              have entryJump : ∀ r, isException r → DataSem.jumpExc entered ≠ none := by
                intro r raised
                simp [DataSem.jumpExc, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed]
              generalize calleeRun : BviSem.evaluate [body] (dataArgs.map dataToBviValue)
                (BviSem.decClock (ticks + 1) smid) = pair
              obtain ⟨calleeResult, calleeState⟩ := pair
              cases calleeResult with
              | val resultValues =>
                simp [calleeRun] at run
                obtain ⟨rfl, rfl⟩ := run
                obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                  compileCalleeFull body dataArgs (BviSem.decClock (ticks + 1) smid) calleeState entered
                    (.val resultValues) recursive calleeRun (by simp) entryRel' entryLocals (entryJump _)
                have projectedResult := calleeOutcome.1 (by simp [isReturn])
                cases result with
                | err error => cases error <;> simp [dataToBviResult] at projectedResult
                | val returned =>
                  have resultEq : resultValues = returned.map dataToBviValue := by
                    simpa [dataToBviResult] using projectedResult.symm
                  have singleton := BviSem.evaluate_singleton body (dataArgs.map dataToBviValue)
                    (BviSem.decClock (ticks + 1) smid) calleeState resultValues calleeRun
                  obtain ⟨sourceValue, singleton⟩ := singleton
                  have lengthOne : returned.length = 1 := by
                    rw [resultEq] at singleton
                    have length := congrArg List.length singleton
                    simpa using length
                  cases returned with
                  | nil => simp at lengthOne
                  | cons dataResult rest =>
                    cases rest with
                    | cons other more => simp at lengthOne
                    | nil =>
                      have sourceResult : resultValues = [dataToBviValue dataResult] := by simpa using resultEq
                      rw [sourceResult] at *
                      have sourceIsResult : isResult (.val resultValues) := ⟨_, rfl⟩
                      obtain ⟨stack, handlerEq0⟩ := calleeOutcome.2.2.1 (Or.inl sourceIsResult)
                      have stackEq : targetNext.stack = .exc tmid.localsSize saved tmid.handler :: tmid.stack := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using stack.symm
                      have handlerEq : targetNext.handler = tmid.stack.length := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using handlerEq0.symm
                      let restored := { targetNext with stack := tmid.stack, locals := saved, localsSize := tmid.localsSize, handler := tmid.handler }
                      have popRun : DataSem.popEnv targetNext = some restored := by simp [DataSem.popEnv, stackEq, restored]
                      generalize handlerCompiled : compileSource (nmid + 1) (nmid :: corr) false live [handler] = triple
                      obtain ⟨handlerCode, handlerValues, n2⟩ := triple
                      have nextBound := compileSource_LESS_EQ (nmid + 1) (nmid :: corr) false live [handler]
                        handlerCode handlerValues n2 handlerCompiled
                      have freshN2 : ∀ k, n2 ≤ k → sptLookup k tmid.locals = none := by
                        intro k bound
                        exact freshMid k (by omega)
                      let moved := DataSem.setVar n2 dataResult restored
                      have setSingleton : DataSem.setVars [n2] [dataResult] restored = moved := by
                        simp [DataSem.setVars, DataSem.setVar, sptFromAList, sptUnion_insert_ln, moved]
                      have relMoved : stateRel calleeState moved := by
                        simpa [stateRel, moved, restored, DataSem.setVar] using finalRel
                      have callOutcome := forceValueOutcome tmid moved n2 corr live env dataResult envVars freshN2
                        (by rfl) (by rfl) (by rfl)
                      let ret := some ([n2], namesOfList (live ++ corr))
                      let after := if tail then DataLang.Prog.return [n2] else .skip
                      let call := DataLang.Prog.call ret dest names
                        (some (nmid, .seq handlerCode (.move n2 (Flapjack.holHd handlerValues))))
                      let inner := DataLang.Prog.seq call after
                      have sourceBound := BviSem.evaluate_clock_le args env s1
                      rw [argsRun] at sourceBound
                      have targetBound : tmid.clock ≤ t1.clock := by
                        simpa [← related.1, ← middleRel.1] using sourceBound
                      have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                      have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                      have codeTimed : DataSem.findCode dest dataValues timed.code timed.stackFrameSizes =
                          some (dataArgs, compileExp dataArgs.length body, size) := by simpa [timed] using targetCode
                      have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                      have clamped : DataSem.fixClock entered ((some (.val [dataResult]) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                          ((some (.val [dataResult]) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                        rw [← targetRun, DataSem.fixClock_evaluate]
                      have callEval : DataSem.evaluate call timed = (none, moved) := by
                        simp [call, ret, DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun,
                          clamped, popRun, setSingleton]
                      have callBound := DataSem.evaluate_clock_le call timed
                      rw [callEval] at callBound
                      cases tail with
                      | false =>
                        refine ⟨moved, .seq first (DataLang.mkTicks ticks inner), none, [n2], n2 + 1,
                          none, ?_, ?_, relMoved, ?_⟩
                        · simp [compileSource, compiled, handlerCompiled, ret, inner, call, after]
                        · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                          rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                          change DataSem.evaluate inner timed = _
                          apply evaluateSeq_continue call after timed moved _ callEval (by simpa using callBound)
                          simp [after, DataSem.evaluate]
                        · exact correctOutcome_seq values (.val [dataToBviValue dataResult]) t1 tmid moved n nmid (n2 + 1)
                            corr live names [n2] env false none ls none firstOutcome
                              (correctOutcome_weaken_start _ tmid moved nmid n2 (n2 + 1) corr live [n2] env false none none (by omega) callOutcome)
                      | true =>
                        let final := DataSem.flushState false moved
                        have movedRead : DataSem.getVar n2 moved.locals = some dataResult := by
                          simp [moved, DataSem.getVar, DataSem.setVar, sptLookup_sptInsert_same]
                        have afterEval : DataSem.evaluate after moved = (some (.val [dataResult]), final) := by
                          simp [after, DataSem.evaluate, DataSem.getVars, movedRead, final]
                        refine ⟨final, .seq first (DataLang.mkTicks ticks inner), some (.val [dataResult]), [n2], n2 + 1,
                          none, ?_, ?_, ?_, ?_⟩
                        · simp [compileSource, compiled, handlerCompiled, ret, inner, call, after]
                        · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                          rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                          change DataSem.evaluate inner timed = _
                          exact evaluateSeq_continue call after timed moved _ callEval (by simpa using callBound) afterEval
                        · simpa [stateRel, final, DataSem.flushState] using relMoved
                        · have stack := callOutcome.2.2.2.2.2.2.2.1
                          have handler := callOutcome.2.2.2.2.2.2.2.2.1
                          have secondOutcome : correctOutcome (.val [dataToBviValue dataResult]) tmid final nmid (n2 + 1)
                              corr live [n2] env true (some (.val [dataResult])) none := by
                            simp [correctOutcome, dataToBviResult, isResult, isReturn, isException, final,
                              DataSem.flushState, stack, handler]
                          exact correctOutcome_seq values (.val [dataToBviValue dataResult]) t1 tmid final n nmid (n2 + 1)
                            corr live names [n2] env true _ ls none firstOutcome secondOutcome
              | err error =>
                cases error with
                | abort reason =>
                  simp [calleeRun] at run
                  obtain ⟨rfl, rfl⟩ := run
                  obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                    compileCalleeFull body dataArgs (BviSem.decClock (ticks + 1) smid) calleeState entered
                      (.err (.abort reason)) recursive calleeRun notType entryRel' entryLocals (entryJump _)
                  have projectedResult := calleeOutcome.1 (by simp [isReturn])
                  have resultEq : result = .err (.abort reason) := by
                    cases result with
                    | val values => simp [dataToBviResult] at projectedResult
                    | err error =>
                      cases error with
                      | abort other => simpa [dataToBviResult] using projectedResult
                      | raise value => simp [dataToBviResult] at projectedResult
                  subst result
                  generalize handlerCompiled : compileSource (nmid + 1) (nmid :: corr) false live [handler] = triple
                  obtain ⟨handlerCode, handlerValues, n2⟩ := triple
                  let ret := some ([n2], namesOfList (live ++ corr))
                  let after := if tail then DataLang.Prog.return [n2] else .skip
                  let call := DataLang.Prog.call ret dest names
                    (some (nmid, .seq handlerCode (.move n2 (Flapjack.holHd handlerValues))))
                  let inner := DataLang.Prog.seq call after
                  have sourceBound := BviSem.evaluate_clock_le args env s1
                  rw [argsRun] at sourceBound
                  have targetBound : tmid.clock ≤ t1.clock := by
                    simpa [← related.1, ← middleRel.1] using sourceBound
                  have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                  have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                  have codeTimed : DataSem.findCode dest dataValues timed.code timed.stackFrameSizes =
                      some (dataArgs, compileExp dataArgs.length body, size) := by simpa [timed] using targetCode
                  have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                  have clamped : DataSem.fixClock entered ((some (.err (.abort reason)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                      ((some (.err (.abort reason)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                    rw [← targetRun, DataSem.fixClock_evaluate]
                  have callEval : DataSem.evaluate call timed = (some (.err (.abort reason)), targetNext) := by
                    simp [call, ret, DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun, clamped]
                  have calleeBound := DataSem.evaluate_clock_le (compileExp dataArgs.length body) entered
                  rw [targetRun] at calleeBound
                  have callBound : targetNext.clock ≤ timed.clock := by
                    simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using Nat.le_trans calleeBound (Nat.sub_le timed.clock 1)
                  have callOutcome : correctOutcome (.err (.abort reason)) tmid targetNext nmid (n2 + 1) corr live [n2] env tail (some (.err (.abort reason))) ls2 := by
                    simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
                  refine ⟨targetNext, .seq first (DataLang.mkTicks ticks inner), some (.err (.abort reason)), [n2], n2 + 1,
                    ls2, ?_, ?_, finalRel, ?_⟩
                  · simp [compileSource, compiled, handlerCompiled, ret, inner, call, after]
                  · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                    rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                    change DataSem.evaluate inner timed = _
                    exact evaluateSeq_stop call after timed targetNext _ callEval callBound
                  · exact correctOutcome_seq values (.err (.abort reason)) t1 tmid targetNext n nmid (n2 + 1)
                      corr live names [n2] env tail _ ls ls2 firstOutcome callOutcome
                | raise raised =>
                  cases raised with
                  | ret values =>
                    simp [calleeRun, BviSem.typeError] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact False.elim (notType rfl)
                  | exn value =>
                    obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                      compileCalleeFull body dataArgs (BviSem.decClock (ticks + 1) smid) calleeState entered
                        (.err (.raise (.exn value))) recursive calleeRun (by simp) entryRel' entryLocals (entryJump _)
                    have projectedResult := calleeOutcome.1 (by simp [isReturn])
                    cases result with
                    | val values => simp [dataToBviResult] at projectedResult
                    | err error =>
                      cases error with
                      | abort reason => simp [dataToBviResult] at projectedResult
                      | raise dataValue =>
                        have valueEq : value = dataToBviValue dataValue := by
                          simpa [dataToBviResult] using projectedResult.symm
                        subst value
                        have raisedResult : isException (.err (.raise (.exn (dataToBviValue dataValue)))) := ⟨_, rfl⟩
                        have jumped := calleeOutcome.2.2.2.2 raisedResult
                        simp [DataSem.jumpExc, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] at jumped
                        obtain ⟨localsEq, localsSizeEq, stackEq, handlerEq⟩ := jumped
                        rw [calleeRun] at run
                        have handlerFacts : BviSem.evaluate [handler] (dataToBviValue dataValue :: env) calleeState = (res, s2) ∧ ¬isReturn res := by
                          cases handlerRun : BviSem.evaluate [handler] (dataToBviValue dataValue :: env) calleeState with
                          | mk outcome next =>
                            cases outcome with
                            | val values =>
                              simp [handlerRun] at run
                              obtain ⟨rfl, rfl⟩ := run
                              exact ⟨rfl, by simp [isReturn]⟩
                            | err error =>
                              cases error with
                              | abort reason =>
                                simp [handlerRun] at run
                                obtain ⟨rfl, rfl⟩ := run
                                exact ⟨rfl, by simp [isReturn]⟩
                              | raise raised =>
                                cases raised with
                                | exn value =>
                                  simp [handlerRun] at run
                                  obtain ⟨rfl, rfl⟩ := run
                                  exact ⟨rfl, by simp [isReturn]⟩
                                | ret values =>
                                  simp [handlerRun, BviSem.typeError] at run
                                  obtain ⟨rfl, rfl⟩ := run
                                  exact False.elim (notType rfl)
                        let handlerStart := DataSem.setVar nmid dataValue targetNext
                        have handlerRel : stateRel calleeState handlerStart := by
                          simpa [stateRel, handlerStart, DataSem.setVar] using finalRel
                        have tempOutcome := forceValueOutcome tmid handlerStart nmid corr live env dataValue envVars freshMid
                          (by simp [handlerStart, DataSem.setVar, ← localsEq, saved])
                          (by simp [handlerStart, DataSem.setVar, ← stackEq])
                          (by simp [handlerStart, DataSem.setVar, ← handlerEq])
                        have tempOutcomeAll := tempOutcome
                        have allLive := correctOutcome_live [dataToBviValue dataValue] tmid handlerStart nmid (nmid + 1)
                          corr live [nmid] env none tempOutcome liveMid
                        have handlerLive : ∀ v ∈ live, sptLookup v handlerStart.locals ≠ none := by
                          intro key member
                          exact allLive key (List.mem_append_right [nmid] member)
                        rcases tempOutcome with ⟨_, _, _, handlerFresh, envAfter, _, _, _, _, handlerJump, resultRel⟩
                        have handlerVars : DataProps.varCorr (dataToBviValue dataValue :: env) (nmid :: corr)
                            (sptMap dataToBviValue handlerStart.locals) := by
                          cases resultRel with
                          | cons lookup _ => exact .cons lookup envAfter
                        have handlerSim := handlerIH values smid (dataArgs.map dataToBviValue) body calleeState
                          (dataToBviValue dataValue) handler valid argsRun found clock calleeRun rfl
                        obtain ⟨handlerNext, handlerCode, handlerPres, handlerNames, n2, ls3, handlerCompiled,
                          handlerTarget, handlerFinalRel, handlerOutcome⟩ :=
                          handlerSim res s2 handlerStart (nmid + 1) (nmid :: corr) false live handlerFacts.1 notType
                            handlerVars (by simp) handlerFresh handlerRel handlerLive
                            (fun raised => handlerJump (jumpMid (exceptionJump raised)))
                        have handlerLength := compileSource_LENGTH (nmid + 1) (nmid :: corr) false live [handler]
                          handlerCode handlerNames n2 handlerCompiled
                        cases handlerNames with
                        | nil => simp at handlerLength
                        | cons handlerName rest =>
                          cases rest with
                          | cons extra rest => simp at handlerLength
                          | nil =>
                            cases handlerPres with
                            | none =>
                              cases res with
                              | err error => simp [correctOutcome] at handlerOutcome
                              | val resultValues =>
                                obtain ⟨resultValue, rfl⟩ := BviSem.evaluate_singleton handler
                                  (dataToBviValue dataValue :: env) calleeState s2 resultValues handlerFacts.1
                                have combined := correctOutcome_let [dataToBviValue dataValue] (.val [resultValue])
                                  tmid handlerStart handlerNext nmid (nmid + 1) n2 corr live [nmid] [handlerName] env
                                  false none none ls3 tempOutcomeAll handlerOutcome
                                obtain ⟨dataResult, moveRun, movedRel, movedOutcome⟩ :=
                                  correctOutcome_move resultValue s2 tmid handlerNext nmid n2 n2 handlerName corr live env
                                    ls3 handlerFinalRel combined (Nat.le_refl n2)
                                let moved := DataSem.setVar n2 dataResult handlerNext
                                have movedRead : DataSem.getVar n2 moved.locals = some dataResult := by
                                  simp [moved, DataSem.getVar, DataSem.setVar, sptLookup_sptInsert_same]
                                have resultProjection : dataToBviValue dataResult = resultValue := by
                                  have resultRel := movedOutcome.2.2.2.2.2.2.2.2.2.2
                                  cases resultRel with
                                  | cons lookup _ =>
                                    simpa [DataSem.getVar, sptLookup_sptMap, moved, DataSem.setVar,
                                      sptLookup_sptInsert_same] using lookup
                                let ret := some ([n2], namesOfList (live ++ corr))
                                let after := if tail then DataLang.Prog.return [n2] else .skip
                                let handlerProg := DataLang.Prog.seq handlerCode (.move n2 handlerName)
                                let call := DataLang.Prog.call ret dest names (some (nmid, handlerProg))
                                let inner := DataLang.Prog.seq call after
                                have sourceBound := BviSem.evaluate_clock_le args env s1
                                rw [argsRun] at sourceBound
                                have targetBound : tmid.clock ≤ t1.clock := by
                                  simpa [← related.1, ← middleRel.1] using sourceBound
                                have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                                have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                                have codeTimed : DataSem.findCode dest dataValues timed.code timed.stackFrameSizes =
                                    some (dataArgs, compileExp dataArgs.length body, size) := by simpa [timed] using targetCode
                                have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                                have handlerSourceBound := BviSem.evaluate_clock_le [handler] (dataToBviValue dataValue :: env) calleeState
                                rw [handlerFacts.1] at handlerSourceBound
                                have handlerTargetBound : handlerNext.clock ≤ handlerStart.clock := by
                                  simpa [← handlerRel.1, ← handlerFinalRel.1] using handlerSourceBound
                                have handlerProgRun : DataSem.evaluate handlerProg handlerStart = (none, moved) :=
                                  evaluateSeq_continue handlerCode (.move n2 handlerName) handlerStart handlerNext _ handlerTarget handlerTargetBound moveRun
                                have clamped : DataSem.fixClock entered ((some (.err (.raise dataValue)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                                    ((some (.err (.raise dataValue)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                                  rw [← targetRun, DataSem.fixClock_evaluate]
                                have callEval : DataSem.evaluate call timed = (none, moved) := by
                                  simp [call, ret, DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun,
                                    clamped, handlerStart, handlerProgRun]
                                have callBound := DataSem.evaluate_clock_le call timed
                                rw [callEval] at callBound
                                cases tail with
                                | false =>
                                  refine ⟨moved, .seq first (DataLang.mkTicks ticks inner), none, [n2], n2 + 1,
                                    none, ?_, ?_, movedRel, ?_⟩
                                  · simp [compileSource, compiled, handlerCompiled, ret, inner, call, handlerProg, after, Flapjack.holHd]
                                  · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                                    rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                                    change DataSem.evaluate inner timed = _
                                    apply evaluateSeq_continue call after timed moved _ callEval (by simpa using callBound)
                                    simp [after, DataSem.evaluate]
                                  · exact correctOutcome_seq values (.val [resultValue]) t1 tmid moved n nmid (n2 + 1)
                                      corr live names [n2] env false none ls none firstOutcome movedOutcome
                                | true =>
                                  let final := DataSem.flushState false moved
                                  have afterEval : DataSem.evaluate after moved = (some (.val [dataResult]), final) := by
                                    simp [after, DataSem.evaluate, DataSem.getVars, movedRead, final]
                                  refine ⟨final, .seq first (DataLang.mkTicks ticks inner), some (.val [dataResult]), [n2], n2 + 1,
                                    none, ?_, ?_, ?_, ?_⟩
                                  · simp [compileSource, compiled, handlerCompiled, ret, inner, call, handlerProg, after, Flapjack.holHd]
                                  · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                                    rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                                    change DataSem.evaluate inner timed = _
                                    exact evaluateSeq_continue call after timed moved _ callEval (by simpa using callBound) afterEval
                                  · simpa [stateRel, final, DataSem.flushState] using movedRel
                                  · have stack := movedOutcome.2.2.2.2.2.2.2.1
                                    have handler := movedOutcome.2.2.2.2.2.2.2.2.1
                                    have secondOutcome : correctOutcome (.val [resultValue]) tmid final nmid (n2 + 1)
                                        corr live [n2] env true (some (.val [dataResult])) none := by
                                      simp [correctOutcome, dataToBviResult, isResult, isReturn, isException, final,
                                        DataSem.flushState, resultProjection, stack, handler, moved]
                                    exact correctOutcome_seq values (.val [resultValue]) t1 tmid final n nmid (n2 + 1)
                                      corr live names [n2] env true _ ls none firstOutcome secondOutcome
                            | some result =>
                              let ret := some ([n2], namesOfList (live ++ corr))
                              let after := if tail then DataLang.Prog.return [n2] else .skip
                              let handlerProg := DataLang.Prog.seq handlerCode (.move n2 handlerName)
                              let call := DataLang.Prog.call ret dest names (some (nmid, handlerProg))
                              let inner := DataLang.Prog.seq call after
                              have sourceBound := BviSem.evaluate_clock_le args env s1
                              rw [argsRun] at sourceBound
                              have targetBound : tmid.clock ≤ t1.clock := by
                                simpa [← related.1, ← middleRel.1] using sourceBound
                              have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                              have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                              have codeTimed : DataSem.findCode dest dataValues timed.code timed.stackFrameSizes =
                                  some (dataArgs, compileExp dataArgs.length body, size) := by simpa [timed] using targetCode
                              have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                              have handlerSourceBound := BviSem.evaluate_clock_le [handler] (dataToBviValue dataValue :: env) calleeState
                              rw [handlerFacts.1] at handlerSourceBound
                              have handlerTargetBound : handlerNext.clock ≤ handlerStart.clock := by
                                simpa [← handlerRel.1, ← handlerFinalRel.1] using handlerSourceBound
                              have handlerProgRun : DataSem.evaluate handlerProg handlerStart = (some result, handlerNext) :=
                                evaluateSeq_stop handlerCode (.move n2 handlerName) handlerStart handlerNext result handlerTarget handlerTargetBound
                              have clamped : DataSem.fixClock entered ((some (.err (.raise dataValue)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                                  ((some (.err (.raise dataValue)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                                rw [← targetRun, DataSem.fixClock_evaluate]
                              have callEval : DataSem.evaluate call timed = (some result, handlerNext) := by
                                simp [call, ret, DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, entered, targetRun,
                                  clamped, handlerStart, handlerProgRun]
                              have callBound := DataSem.evaluate_clock_le call timed
                              rw [callEval] at callBound
                              have secondOutcome : correctOutcome res tmid handlerNext nmid (n2 + 1) corr live [n2] env tail (some result) ls3 := by
                                rcases handlerOutcome with ⟨projection, returned, control, tailResult, exception⟩
                                refine ⟨projection, returned, ?_, ?_, ?_⟩
                                · intro resultOrReturn
                                  simpa [handlerStart, DataSem.setVar, ← stackEq, ← handlerEq] using control resultOrReturn
                                · intro isResult
                                  have impossible := tailResult isResult
                                  contradiction
                                · intro raised
                                  simpa [handlerStart, DataSem.setVar, ← stackEq, ← handlerEq] using exception raised
                              refine ⟨handlerNext, .seq first (DataLang.mkTicks ticks inner), some result, [n2], n2 + 1,
                                ls3, ?_, ?_, handlerFinalRel, ?_⟩
                              · simp [compileSource, compiled, handlerCompiled, ret, inner, call, handlerProg, after, Flapjack.holHd]
                              · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                                rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                                change DataSem.evaluate inner timed = _
                                exact evaluateSeq_stop call after timed handlerNext result callEval (by simpa using callBound)
                              · exact correctOutcome_seq values res t1 tmid handlerNext n nmid (n2 + 1)
                                  corr live names [n2] env tail _ ls ls3 firstOutcome secondOutcome
  · simp only [not_not] at valid
    have bad : BviSem.evaluate [.call ticks dest args handler] env s1 =
        (.err (.abort .typeError), s1) := by
      simp [BviSem.evaluate, valid]
    rw [bad] at run
    cases run
    exact False.elim (notType rfl)
end Flapjack.Compiler.Backend.BviToData
