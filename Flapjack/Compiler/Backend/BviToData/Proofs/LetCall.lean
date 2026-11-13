module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CallCorrect
public import Flapjack.Compiler.Backend.BviToData.Proofs.Call

@[expose] public section

/-! The complete LetCall case of the BVI-to-data compiler simulation. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem tupleLookup {α : Type} (values : List α) (start key : Nat) :
    sptLookup key (sptFromAList ((List.range' start values.length).zip values)) =
      if start ≤ key then values[key - start]? else none := by
  rw [sptLookup_sptFromAList]
  induction values generalizing start with
  | nil => simp [sptAListLookup]
  | cons value rest ih =>
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, sptAListLookup]
    by_cases eq : key = start
    · subst key
      simp
    · simp only [eq, ↓reduceIte]
      rw [ih]
      by_cases bound : start ≤ key
      · have greater : start + 1 ≤ key := by omega
        have diff : key - start = (key - (start + 1)) + 1 := by omega
        simp [bound, greater, diff]
      · have greater : ¬start + 1 ≤ key := by omega
        simp [bound, greater]

private theorem tupleOutcome {C F : Type} (target next : DataSem.State C F)
    (n : Nat) (corr live : List Nat) (env : List BvlSem.Value) (values : List DataSem.Value)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k target.locals = none)
    (locals : next.locals = sptUnion (sptFromAList ((List.range' n values.length).zip values))
      (sptMkWf (sptInter target.locals (namesOfList (live ++ corr)))))
    (stack : next.stack = target.stack) (handler : next.handler = target.handler) :
    correctOutcome (.val (values.map dataToBviValue)) target next n (n + values.length) corr live
      (List.range' n values.length) env false none none := by
  have mappedReads := DataProps.getVars_thm corr env (sptMap dataToBviValue target.locals) vars
  have corrPresent : ∀ key ∈ corr, sptLookup key target.locals ≠ none := by
    intro key member absent
    have mapped := getVars_present corr (sptMap dataToBviValue target.locals) env mappedReads key member
    simp [sptLookup_sptMap, absent] at mapped
  let saved := sptMkWf (sptInter target.locals (namesOfList (live ++ corr)))
  have lookupNext (key : Nat) : sptLookup key next.locals =
      match (if n ≤ key then values[key - n]? else none) with
      | some value => some value
      | none => sptLookup key saved := by
    rw [locals, sptLookup_sptUnion, tupleLookup]
    by_cases bound : n ≤ key
    · cases found : values[key - n]? <;> simp [bound, saved]
    · simp [bound, saved]
  simp only [correctOutcome, true_and]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, stack.symm, handler.symm, ?_, ?_⟩
  · intro key member
    simp only [List.mem_range'] at member
    omega
  · intro key bound
    rw [lookupNext]
    have above : n ≤ key := by omega
    have absent : values[key - n]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [above, absent, saved, lookup_cut_namesOfList, fresh key above]
  · apply varCorr_of_lookup_eq dataToBviValue target.locals next.locals corr env vars
    intro key member
    have below : key < n := by
      by_contra bound
      exact corrPresent key member (fresh key (by omega))
    rw [lookupNext]
    simp [Nat.not_le_of_gt below, saved, lookup_cut_namesOfList, member]
  · intro key value found
    by_cases below : key < n
    · omega
    · have above : n ≤ key := by omega
      rw [lookupNext] at found
      cases element : values[key - n]? with
      | none => simp [above, element, saved, lookup_cut_namesOfList, fresh key above] at found
      | some item =>
        have indexBound := List.getElem?_eq_some_iff.mp element |>.1
        omega
  · intro key value found needed
    have below : key < n := by
      by_contra bound
      have absent := fresh key (by omega)
      rw [found] at absent
      contradiction
    have kept : key ∈ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [lookupNext]
    simp [Nat.not_le_of_gt below, saved, lookup_cut_namesOfList, kept, found]
  · intro available
    cases run : DataSem.jumpExc target with
    | none => exact False.elim (available run)
    | some jumped =>
      have transported := DataSem.jumpExc_transport target next jumped stack handler run
      rw [transported]
      simp
  · apply List.forall₂_iff_get.mpr
    constructor
    · simp
    · intro index leftBound rightBound
      have bound : index < values.length := by simpa using rightBound
      simp [DataSem.getVar, sptLookup_sptMap, lookupNext, bound]

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace LetCallCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end LetCallCarrier

/-- LetCall case of compiler correctness, using the guarded recursive induction
hypotheses from the BVI evaluator. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem simulationFor_letCall {C F : Type} (rets ticks dest : Nat)
    (args : List Bvi.Exp) (body : Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F) (argsIH : simulationFor args env s1)
    (calleeIH : ∀ values state callArgs callee,
      BviSem.evaluate args env s1 = (.val values, state) →
      BvlSem.findCode (some dest) values state.code = some (callArgs, callee) →
      ¬(state.clock < ticks + 1) →
      simulationFor [callee] callArgs (BviSem.decClock (ticks + 1) state))
    (bodyIH : ∀ values state callArgs callee resultState returned,
      BviSem.evaluate args env s1 = (.val values, state) →
      BvlSem.findCode (some dest) values state.code = some (callArgs, callee) →
      ¬(state.clock < ticks + 1) →
      BviSem.evaluate [callee] callArgs (BviSem.decClock (ticks + 1) state) =
        (.err (.raise (.ret returned)), resultState) → returned.length = rets →
      simulationFor [body] (returned ++ env) resultState) :
    simulationFor [.letCall rets ticks dest args body] env s1 := by
  intro res s2 t1 n corr tail live run notType vars tailShape fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argsResult, smid⟩ := pair
  cases argsResult with
  | err error =>
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨t2, first, pres, names, nmid, ls, compiled, target, finalRel, outcome⟩ :=
      argsIH (.err error) smid t1 n corr false live argsRun notType vars (by simp) fresh related livePresent exceptionJump
    cases pres with
    | none => simp [correctOutcome] at outcome
    | some result =>
      have sourceBound := BviSem.evaluate_clock_le args env s1
      rw [argsRun] at sourceBound
      have targetBound : t2.clock ≤ t1.clock := by
        simpa [← related.1, ← finalRel.1] using sourceBound
      by_cases direct : body = .return ((List.range rets).map Bvi.Exp.var)
      · let call := DataLang.Prog.call none (some dest) names none
        refine ⟨t2, .seq first (DataLang.mkTicks ticks call), some result, [nmid], nmid + 1, ls,
          ?_, ?_, finalRel, ?_⟩
        · simp [compileSource, compiled, direct, call]
        · exact evaluateSeq_stop first _ t1 t2 result target targetBound
        · simpa [correctOutcome, isResult] using outcome
      · let returns := (List.range rets).map (nmid + ·)
        generalize bodyCompiled : compileSource (nmid + rets) (returns ++ corr) tail live [body] = triple
        obtain ⟨bodyCode, bodyNames, n2⟩ := triple
        let ret := some (returns, namesOfList (live ++ corr))
        let call := DataLang.Prog.call ret (some dest) names none
        let inner := DataLang.Prog.seq first (DataLang.mkTicks ticks call)
        refine ⟨t2, .seq inner bodyCode, some result, bodyNames, n2, ls, ?_, ?_, finalRel, ?_⟩
        · simp [compileSource, compiled, direct, bodyCompiled, ret, call, inner, returns]
        · have innerRun : DataSem.evaluate inner t1 = (some result, t2) :=
            evaluateSeq_stop first (DataLang.mkTicks ticks call) t1 t2 result target targetBound
          exact evaluateSeq_stop inner bodyCode t1 t2 result innerRun targetBound
        · simpa [correctOutcome, isResult] using outcome
  | val values =>
    obtain ⟨tmid, first, pres, names, nmid, ls, compiled, target, middleRel, outcome⟩ :=
      argsIH (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
        (by simp [isException])
    cases pres with
    | some result => simp [correctOutcome, isResult] at outcome
    | none =>
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
      cases found : BvlSem.findCode (some dest) values smid.code with
      | none =>
        simp [found, BviSem.typeError] at run
        exact False.elim (notType run.1.symm)
      | some pair =>
        obtain ⟨callArgs, callee⟩ := pair
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
            by_cases direct : body = .return ((List.range rets).map Bvi.Exp.var)
            · let call := DataLang.Prog.call none (some dest) names none
              refine ⟨final, .seq first (DataLang.mkTicks ticks call), some (.err (.abort .timeoutError)),
                [nmid], nmid + 1, none, ?_, ?_, ?_, ?_⟩
              · simp [compileSource, compiled, direct, call]
              · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                simp [DataSem.evaluate_mkTicks, earlyTarget, final]
              · simpa [stateRel, final] using middleRel.2
              · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
            · let returns := (List.range rets).map (nmid + ·)
              generalize bodyCompiled : compileSource (nmid + rets) (returns ++ corr) tail live [body] = triple
              obtain ⟨bodyCode, bodyNames, n2⟩ := triple
              let ret := some (returns, namesOfList (live ++ corr))
              let call := DataLang.Prog.call ret (some dest) names none
              let inner := DataLang.Prog.seq first (DataLang.mkTicks ticks call)
              have innerRun : DataSem.evaluate inner t1 = (some (.err (.abort .timeoutError)), final) := by
                apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                simp [DataSem.evaluate_mkTicks, earlyTarget, final]
              refine ⟨final, .seq inner bodyCode, some (.err (.abort .timeoutError)), bodyNames, n2, none,
                ?_, ?_, ?_, ?_⟩
              · simp [compileSource, compiled, direct, bodyCompiled, ret, call, inner, returns]
              · apply evaluateSeq_stop inner bodyCode t1 final _ innerRun
                simp [final]
              · simpa [stateRel, final] using middleRel.2
              · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
          · have sourceEq : smid.clock = ticks := by omega
            have targetEq : tmid.clock = ticks := by rw [← middleRel.1, sourceEq]
            have liveMidAll := correctOutcome_live values t1 tmid n nmid corr live names env ls outcome livePresent
            have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
              intro v member
              exact liveMidAll v (List.mem_append_right names member)
            rcases outcome with ⟨_, _, _, _, envVars, _, _, _, _, _, resultVars⟩
            obtain ⟨dataValues, dataRead, projected⟩ := getVars_lift names values tmid.locals resultVars
            have foundProjected : BvlSem.findCode (some dest) (dataValues.map dataToBviValue) smid.code = some (callArgs, callee) := by
              simpa [projected] using found
            obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
              findCode_projection (some dest) dataValues smid tmid callArgs callee middleRel foundProjected
            have rootsPresent : ∀ key ∈ live ++ corr, sptLookup key tmid.locals ≠ none := by
              simpa [DataSem.getVars] using
                (roots_present tmid [] live corr env [] envVars liveMid (by simp [DataSem.getVars]))
            let saved := sptMkWf (sptInter tmid.locals (namesOfList (live ++ corr)))
            have cut : DataSem.cutEnv (namesOfList (live ++ corr)) tmid.locals = some saved :=
              cutEnv_namesOfList (live ++ corr) tmid.locals rootsPresent
            let timed := { tmid with clock := 0 }
            by_cases direct : body = .return ((List.range rets).map Bvi.Exp.var)
            · let call := DataLang.Prog.call none (some dest) names none
              let final := DataSem.flushState true timed
              refine ⟨final, .seq first (DataLang.mkTicks ticks call), some (.err (.abort .timeoutError)),
                [nmid], nmid + 1, none, ?_, ?_, ?_, ?_⟩
              · simp [compileSource, compiled, direct, call]
              · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                simp [DataSem.evaluate_mkTicks, targetEq, timed, call, DataSem.evaluate, dataRead, targetCode, final]
              · simpa [stateRel, final, DataSem.flushState, timed] using middleRel.2
              · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
            · let returns := (List.range rets).map (nmid + ·)
              have nodup : returns.Nodup := by
                apply List.Nodup.map
                · intro a b same
                  exact Nat.add_left_cancel same
                · exact List.nodup_range
              generalize bodyCompiled : compileSource (nmid + rets) (returns ++ corr) tail live [body] = triple
              obtain ⟨bodyCode, bodyNames, n2⟩ := triple
              let ret := some (returns, namesOfList (live ++ corr))
              let call := DataLang.Prog.call ret (some dest) names none
              let inner := DataLang.Prog.seq first (DataLang.mkTicks ticks call)
              let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock timed))
              let final := { entered with stack := [], locals := .ln }
              have innerRun : DataSem.evaluate inner t1 = (some (.err (.abort .timeoutError)), final) := by
                apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                simp [DataSem.evaluate_mkTicks, targetEq, timed, call, ret, DataSem.evaluate, dataRead, targetCode,
                  cut, nodup, entered, final]
              refine ⟨final, .seq inner bodyCode, some (.err (.abort .timeoutError)), bodyNames, n2, none,
                ?_, ?_, ?_, ?_⟩
              · simp [compileSource, compiled, direct, bodyCompiled, ret, call, inner, returns]
              · apply evaluateSeq_stop inner bodyCode t1 final _ innerRun
                simp [final, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed]
              · simpa [stateRel, final, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using middleRel.2
              · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
        · have firstOutcome := outcome
          have liveMidAll := correctOutcome_live values t1 tmid n nmid corr live names env ls outcome livePresent
          have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
            intro v member
            exact liveMidAll v (List.mem_append_right names member)
          rcases outcome with ⟨_, _, _, freshMid, envVars, _, _, _, _, jumpMid, resultVars⟩
          obtain ⟨dataValues, dataRead, projected⟩ := getVars_lift names values tmid.locals resultVars
          have foundProjected : BvlSem.findCode (some dest) (dataValues.map dataToBviValue) smid.code = some (callArgs, callee) := by
            simpa [projected] using found
          obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
            findCode_projection (some dest) dataValues smid tmid callArgs callee middleRel foundProjected
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
          have recursive := calleeIH values smid callArgs callee argsRun found clock
          simp only [found, if_neg clock] at run
          rw [BviSem.fixClock_evaluate] at run
          subst callArgs
          cases calleeRun : BviSem.evaluate [callee] (dataArgs.map dataToBviValue) (BviSem.decClock (ticks + 1) smid) with
          | mk calleeResult calleeState =>
            cases calleeResult with
            | val values =>
              simp [calleeRun, BviSem.typeError] at run
              obtain ⟨rfl, rfl⟩ := run
              exact False.elim (notType rfl)
            | err error =>
              by_cases returned : isReturn (.err error)
              · cases error with
                | abort reason => simp [isReturn] at returned
                | raise raised =>
                  cases raised with
                  | exn value => simp [isReturn] at returned
                  | ret returnedValues =>
                    by_cases count : returnedValues.length = rets
                    · simp only [calleeRun, if_pos count] at run
                      have bodyRun : BviSem.evaluate [body] (returnedValues ++ env) calleeState = (res, s2) := run
                      have sourceBound := BviSem.evaluate_clock_le args env s1
                      rw [argsRun] at sourceBound
                      have targetBound : tmid.clock ≤ t1.clock := by
                        simpa [← related.1, ← middleRel.1] using sourceBound
                      have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                      have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                      have codeTimed : DataSem.findCode (some dest) dataValues timed.code timed.stackFrameSizes =
                          some (dataArgs, compileExp dataArgs.length callee, size) := by simpa [timed] using targetCode
                      by_cases direct : body = .return ((List.range rets).map Bvi.Exp.var)
                      · subst body
                        have bodyReturn := evaluate_return_range rets returnedValues env calleeState count
                        change BviSem.evaluate [.return ((List.range rets).map Bvi.Exp.var)] (returnedValues ++ env) calleeState = _ at bodyReturn
                        rw [bodyReturn] at bodyRun
                        cases bodyRun
                        let entered := DataSem.callEnv dataArgs size (DataSem.decClock timed)
                        have entryLocals : entered.locals = sptFromList dataArgs := rfl
                        obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                          compileCalleeFull callee dataArgs (BviSem.decClock (ticks + 1) smid) s2 entered
                            (.err (.raise (.ret returnedValues))) recursive calleeRun (by simp) entryRel entryLocals (by simp [isException])
                        have isRet : isReturn (.err (.raise (.ret returnedValues))) := ⟨_, rfl⟩
                        obtain ⟨resultValues, resultEq, returnedEq⟩ := calleeOutcome.2.1 isRet
                        subst result
                        have projected : returnedValues = resultValues.map dataToBviValue := by simpa using returnedEq
                        have secondOutcome : correctOutcome (.err (.raise (.ret returnedValues))) tmid targetNext nmid (nmid + 1)
                            corr live [nmid] env tail (some (.val resultValues)) ls2 := by
                          refine ⟨?_, ?_, ?_, ?_, ?_⟩
                          · intro notRet
                            exact False.elim (notRet isRet)
                          · intro _
                            exact ⟨resultValues, rfl, by simp [projected]⟩
                          · intro resultOrReturn
                            simpa [entered, DataSem.callEnv, DataSem.decClock, timed] using calleeOutcome.2.2.1 resultOrReturn
                          · intro impossible
                            rcases impossible with ⟨_, equality⟩
                            cases equality
                          · intro impossible
                            rcases impossible with ⟨_, equality⟩
                            cases equality
                        let call := DataLang.Prog.call none (some dest) names none
                        refine ⟨targetNext, .seq first (DataLang.mkTicks ticks call), some (.val resultValues), [nmid], nmid + 1,
                          ls2, ?_, ?_, finalRel, ?_⟩
                        · simp [compileSource, compiled, call]
                        · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                          rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                          change DataSem.evaluate call timed = _
                          simp [call, DataSem.evaluate, readTimed, codeTimed, timedNonzero, entered, targetRun]
                        · exact correctOutcome_seq values (.err (.raise (.ret returnedValues))) t1 tmid targetNext n nmid (nmid + 1)
                            corr live names [nmid] env tail _ ls ls2 firstOutcome secondOutcome
                      · let returns := (List.range rets).map (nmid + ·)
                        have nodup : returns.Nodup := by
                          apply List.Nodup.map
                          · intro a b same
                            exact Nat.add_left_cancel same
                          · exact List.nodup_range
                        generalize bodyCompiled : compileSource (nmid + rets) (returns ++ corr) tail live [body] = triple
                        obtain ⟨bodyCode, bodyNames, n2⟩ := triple
                        let ret := some (returns, namesOfList (live ++ corr))
                        let call := DataLang.Prog.call ret (some dest) names none
                        let inner := DataLang.Prog.seq first (DataLang.mkTicks ticks call)
                        let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock timed))
                        have entryRel' : stateRel (BviSem.decClock (ticks + 1) smid) entered := by
                          simpa [stateRel, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using entryRel
                        have entryLocals : entered.locals = sptFromList dataArgs := rfl
                        obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                          compileCalleeFull callee dataArgs (BviSem.decClock (ticks + 1) smid) calleeState entered
                            (.err (.raise (.ret returnedValues))) recursive calleeRun (by simp) entryRel' entryLocals (by simp [isException])
                        have isRet : isReturn (.err (.raise (.ret returnedValues))) := ⟨_, rfl⟩
                        obtain ⟨resultValues, resultEq, returnedEq⟩ := calleeOutcome.2.1 isRet
                        subst result
                        have projected : returnedValues = resultValues.map dataToBviValue := by simpa using returnedEq
                        have lengthEq : resultValues.length = rets := by
                          have length := congrArg List.length projected
                          simpa [count] using length.symm
                        have returnsEq : returns = List.range' nmid resultValues.length := by
                          simp [returns, lengthEq, List.range'_eq_map_range]
                        obtain ⟨stack, handler⟩ := calleeOutcome.2.2.1 (Or.inr isRet)
                        have stackEq : targetNext.stack = .env tmid.localsSize saved :: tmid.stack := by
                          simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using stack.symm
                        have handlerEq : targetNext.handler = tmid.handler := by
                          simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using handler.symm
                        let restored := { targetNext with stack := tmid.stack, locals := saved, localsSize := tmid.localsSize }
                        have popRun : DataSem.popEnv targetNext = some restored := by simp [DataSem.popEnv, stackEq, restored]
                        let moved := DataSem.setVars returns resultValues restored
                        have movedRel : stateRel calleeState moved := by
                          simpa [stateRel, moved, restored, DataSem.setVars] using finalRel
                        have tuple := tupleOutcome tmid moved nmid corr live env resultValues envVars freshMid
                          (by simp [moved, DataSem.setVars, restored, saved, returnsEq])
                          (by rfl) (by simpa [moved, restored, DataSem.setVars] using handlerEq)
                        have tupleLiveAll := correctOutcome_live (resultValues.map dataToBviValue) tmid moved nmid
                          (nmid + resultValues.length) corr live (List.range' nmid resultValues.length) env none tuple liveMid
                        have tupleLive : ∀ v ∈ live, sptLookup v moved.locals ≠ none := by
                          intro key member
                          exact tupleLiveAll key (List.mem_append_right _ member)
                        have tupleAll := tuple
                        rcases tuple with ⟨_, _, _, tupleFresh, tupleEnv, _, _, _, _, tupleJump, tupleVars⟩
                        have bodyVars : DataProps.varCorr (returnedValues ++ env) (returns ++ corr)
                            (sptMap dataToBviValue moved.locals) := by
                          rw [projected, returnsEq]
                          exact varCorr_append tupleVars tupleEnv
                        have bodySim := bodyIH values smid (dataArgs.map dataToBviValue) callee calleeState returnedValues
                          argsRun found clock calleeRun count
                        obtain ⟨targetFinal, bodyProg, bodyPres, bodyNames', next, ls3, bodyCompiled',
                          bodyTarget, bodyRel, bodyOutcome⟩ :=
                          bodySim res s2 moved (nmid + rets) (returns ++ corr) tail live bodyRun notType bodyVars
                            (by simp) (by simpa [lengthEq] using tupleFresh) movedRel tupleLive
                            (fun raised => tupleJump (jumpMid (exceptionJump raised)))
                        rw [bodyCompiled] at bodyCompiled'
                        simp only [Prod.mk.injEq] at bodyCompiled'
                        obtain ⟨rfl, rfl, rfl⟩ := bodyCompiled'
                        have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                        have clamped : DataSem.fixClock entered ((some (.val resultValues) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                            ((some (.val resultValues) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                          rw [← targetRun, DataSem.fixClock_evaluate]
                        have callEval : DataSem.evaluate call timed = (none, moved) := by
                          simp [call, ret, DataSem.evaluate, readTimed, codeTimed, cutTimed, timedNonzero, nodup,
                            entered, targetRun, clamped, popRun, moved, lengthEq, returns]
                        have innerRun : DataSem.evaluate inner t1 = (none, moved) := by
                          apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                          rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                          change DataSem.evaluate call timed = _
                          exact callEval
                        have innerBound := DataSem.evaluate_clock_le inner t1
                        rw [innerRun] at innerBound
                        have secondOutcome : correctOutcome res tmid targetFinal nmid n2 corr live bodyNames env tail bodyPres ls3 := by
                          apply correctOutcome_let (resultValues.map dataToBviValue) res tmid moved targetFinal nmid
                            (nmid + resultValues.length) n2 corr live (List.range' nmid resultValues.length) bodyNames env tail bodyPres none ls3
                            tupleAll
                          simpa [projected, returnsEq, lengthEq] using bodyOutcome
                        refine ⟨targetFinal, .seq inner bodyCode, bodyPres, bodyNames, n2, ls3, ?_, ?_, bodyRel, ?_⟩
                        · simp [compileSource, compiled, direct, bodyCompiled, ret, call, inner, returns]
                        · exact evaluateSeq_continue inner bodyCode t1 moved _ innerRun (by simpa using innerBound) bodyTarget
                        · exact correctOutcome_seq values res t1 tmid targetFinal n nmid n2 corr live names bodyNames env tail
                            bodyPres ls ls3 firstOutcome secondOutcome
                    · simp [calleeRun, count, BviSem.typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact False.elim (notType rfl)
              · have resultEq : res = .err error ∧ s2 = calleeState := by
                  cases error with
                  | abort reason => simpa [calleeRun] using run.symm
                  | raise raised =>
                    cases raised with
                    | exn value => simpa [calleeRun] using run.symm
                    | ret values => simp [isReturn] at returned
                obtain ⟨rfl, rfl⟩ := resultEq
                have sourceBound := BviSem.evaluate_clock_le args env s1
                rw [argsRun] at sourceBound
                have targetBound : tmid.clock ≤ t1.clock := by
                  simpa [← related.1, ← middleRel.1] using sourceBound
                have ticksEnough : ¬tmid.clock < ticks := by have h := middleRel.1; omega
                have readTimed : DataSem.getVars names timed.locals = some dataValues := by simpa [timed] using dataRead
                have codeTimed : DataSem.findCode (some dest) dataValues timed.code timed.stackFrameSizes =
                    some (dataArgs, compileExp dataArgs.length callee, size) := by simpa [timed] using targetCode
                have cutTimed : DataSem.cutEnv (namesOfList (live ++ corr)) timed.locals = some saved := by simpa [timed] using cut
                by_cases direct : body = .return ((List.range rets).map Bvi.Exp.var)
                · let entered := DataSem.callEnv dataArgs size (DataSem.decClock timed)
                  have entryLocals : entered.locals = sptFromList dataArgs := rfl
                  have entryJump : isException (.err error) → DataSem.jumpExc entered ≠ none := by
                    intro raised
                    have available := jumpMid (exceptionJump raised)
                    cases oldJump : DataSem.jumpExc tmid with
                    | none => exact False.elim (available oldJump)
                    | some jumped =>
                      have transported := DataSem.jumpExc_transport tmid entered jumped rfl rfl oldJump
                      rw [transported]
                      simp
                  obtain ⟨targetNext, result, ls2, targetRun, finalRel, calleeOutcome⟩ :=
                    compileCalleeFull callee dataArgs (BviSem.decClock (ticks + 1) smid) s2 entered (.err error)
                      recursive calleeRun notType entryRel entryLocals entryJump
                  have secondOutcome : correctOutcome (.err error) tmid targetNext nmid (nmid + 1) corr live [nmid] env tail (some result) ls2 := by
                    rcases calleeOutcome with ⟨projection, returnClause, control, _, exception⟩
                    refine ⟨projection, returnClause, ?_, ?_, ?_⟩
                    · intro resultOrReturn
                      simpa [entered, DataSem.callEnv, DataSem.decClock, timed] using control resultOrReturn
                    · intro impossible
                      rcases impossible with ⟨_, equality⟩
                      cases equality
                    · intro raised
                      simpa [entered, DataSem.callEnv, DataSem.decClock, timed] using exception raised
                  let call := DataLang.Prog.call none (some dest) names none
                  refine ⟨targetNext, .seq first (DataLang.mkTicks ticks call), some result, [nmid], nmid + 1,
                    ls2, ?_, ?_, finalRel, ?_⟩
                  · simp [compileSource, compiled, direct, call]
                  · apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                    rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                    change DataSem.evaluate call timed = _
                    simp [call, DataSem.evaluate, readTimed, codeTimed, timedNonzero, entered, targetRun]
                  · exact correctOutcome_seq values (.err error) t1 tmid targetNext n nmid (nmid + 1) corr live names [nmid]
                      env tail _ ls ls2 firstOutcome secondOutcome
                · let returns := (List.range rets).map (nmid + ·)
                  have nodup : returns.Nodup := by
                    apply List.Nodup.map
                    · intro a b same
                      exact Nat.add_left_cancel same
                    · exact List.nodup_range
                  generalize bodyCompiled : compileSource (nmid + rets) (returns ++ corr) tail live [body] = triple
                  obtain ⟨bodyCode, bodyNames, n2⟩ := triple
                  let ret := some (returns, namesOfList (live ++ corr))
                  let call := DataLang.Prog.call ret (some dest) names none
                  let inner := DataLang.Prog.seq first (DataLang.mkTicks ticks call)
                  let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock timed))
                  have entryRel' : stateRel (BviSem.decClock (ticks + 1) smid) entered := by
                    simpa [stateRel, entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using entryRel
                  have entryLocals : entered.locals = sptFromList dataArgs := rfl
                  have entryJump : isException (.err error) → DataSem.jumpExc entered ≠ none := by
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
                    compileCalleeFull callee dataArgs (BviSem.decClock (ticks + 1) smid) s2 entered (.err error)
                      recursive calleeRun notType entryRel' entryLocals entryJump
                  have projectedResult := calleeOutcome.1 returned
                  have resultError : ∃ dataError, result = .err dataError := by
                    cases result with
                    | val values => simp [dataToBviResult] at projectedResult
                    | err dataError => exact ⟨dataError, rfl⟩
                  obtain ⟨dataError, rfl⟩ := resultError
                  have secondOutcome : correctOutcome (.err error) tmid targetNext nmid n2 corr live bodyNames env tail (some (.err dataError)) ls2 := by
                    refine ⟨fun _ => projectedResult, fun isRet => False.elim (returned isRet), ?_, ?_, ?_⟩
                    · intro resultOrReturn
                      rcases resultOrReturn with result | ret
                      · rcases result with ⟨_, equality⟩
                        cases equality
                      · exact False.elim (returned ret)
                    · intro impossible
                      rcases impossible with ⟨_, equality⟩
                      cases equality
                    · intro raised
                      have calleeJump := calleeOutcome.2.2.2.2 raised
                      have jumpRun : DataSem.jumpExc { targetNext with stack := .env tmid.localsSize saved :: tmid.stack, handler := tmid.handler } =
                          some { targetNext with localsSize := ls2 } := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, timed] using calleeJump
                      exact jumpExc_stripSaved tmid targetNext saved ls2 (jumpMid (exceptionJump raised)) jumpRun
                  have clamped : DataSem.fixClock entered ((some (.err dataError) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                      ((some (.err dataError) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                    rw [← targetRun, DataSem.fixClock_evaluate]
                  have callEval : DataSem.evaluate call timed = (some (.err dataError), targetNext) := by
                    cases dataError <;> simp [call, ret, DataSem.evaluate, readTimed, codeTimed, cutTimed,
                      timedNonzero, nodup, entered, targetRun, clamped]
                  have innerRun : DataSem.evaluate inner t1 = (some (.err dataError), targetNext) := by
                    apply evaluateSeq_continue first _ t1 tmid _ target targetBound
                    rw [DataSem.evaluate_mkTicks, if_neg ticksEnough]
                    change DataSem.evaluate call timed = _
                    exact callEval
                  have innerBound := DataSem.evaluate_clock_le inner t1
                  rw [innerRun] at innerBound
                  refine ⟨targetNext, .seq inner bodyCode, some (.err dataError), bodyNames, n2,
                    ls2, ?_, ?_, finalRel, ?_⟩
                  · simp [compileSource, compiled, direct, bodyCompiled, ret, call, inner, returns]
                  · exact evaluateSeq_stop inner bodyCode t1 targetNext _ innerRun (by simpa using innerBound)
                  · exact correctOutcome_seq values (.err error) t1 tmid targetNext n nmid n2 corr live names bodyNames
                      env tail _ ls ls2 firstOutcome secondOutcome
end Flapjack.Compiler.Backend.BviToData
