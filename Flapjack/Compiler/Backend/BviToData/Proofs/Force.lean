module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Callee
public import Flapjack.Compiler.Backend.BviToData.Proofs.Thunk
public import Flapjack.Compiler.Backend.BviToData.Proofs.FindCode
public import Flapjack.Compiler.Backend.BviToData.Proofs.Optimise
public import Flapjack.Compiler.Backend.BviToData.Proofs.Jump
public import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
public import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
public import Flapjack.Misc.Sptree.FromList.Domain
public import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush

@[expose] public section

/-! The complete Force case of the BVI-to-data compiler simulation. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace ForceCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end ForceCarrier

/-- Force case of compiler correctness, with the guarded recursive callee
induction hypothesis from the BVI evaluator. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem simulationFor_force {C F : Type} (location index : Nat) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F)
    (calleeIH : ∀ thunk function args body,
      env[index]? = some thunk →
      BviSem.destThunk thunk s1.refs = .isThunk .notEvaluated function →
      BvlSem.findCode (some location) [thunk, function] s1.code = some (args, body) →
      s1.clock ≠ 0 → simulationFor [body] args (BviSem.decClock 1 s1)) :
    simulationFor [.force location index] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  cases atIndex : env[index]? with
  | none =>
    simp [BviSem.evaluate, atIndex] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notTypeError rfl)
  | some thunk =>
    obtain ⟨name, nameAt, valueAt⟩ := DataProps.varCorr_lookup env corr
      (sptMap dataToBviValue t1.locals) vars index thunk atIndex
    have valueAt' : (sptLookup name t1.locals).map dataToBviValue = some thunk := by
      simpa [DataSem.getVar, sptLookup_sptMap] using valueAt
    cases lookup : sptLookup name t1.locals with
    | none => simp [lookup] at valueAt'
    | some dataThunk =>
      have projected : dataToBviValue dataThunk = thunk := by simpa [lookup] using valueAt'
      have dataRead : DataSem.getVar name t1.locals = some dataThunk := lookup
      cases inspect : BviSem.destThunk thunk s1.refs with
      | badRef =>
        simp [BviSem.evaluate, atIndex, inspect] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notTypeError rfl)
      | notThunk =>
        simp [BviSem.evaluate, atIndex, inspect] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notTypeError rfl)
      | isThunk mode value =>
        have inspect' : BviSem.destThunk (dataToBviValue dataThunk) s1.refs = .isThunk mode value := by
          simpa [projected] using inspect
        obtain ⟨dataValue, dataInspect, dataProjected⟩ := stateRel_destThunk s1 t1 dataThunk mode value related inspect'
        cases mode with
        | evaluated =>
          simp [BviSem.evaluate, atIndex, inspect] at run
          obtain ⟨rfl, rfl⟩ := run
          cases tail with
          | true =>
            refine ⟨DataSem.flushState false t1, .force none location name, some (.val [dataValue]), [n], max (n + 1) (name + 1), none, ?_, ?_, ?_, ?_⟩
            · simp [compileSource, nameAt]
            · simp [DataSem.evaluate, dataRead, dataInspect]
            · simpa [stateRel, DataSem.flushState] using related
            · simp [correctOutcome, isReturn, isResult, isException, dataToBviResult, dataProjected, DataSem.flushState]
          | false =>
            have nameBelow : name < n := by
              by_contra h
              have absent := fresh name (by omega)
              simp [lookup] at absent
            have nextEq : max (n + 1) (name + 1) = n + 1 := by omega
            have mappedReads := DataProps.getVars_thm corr env (sptMap dataToBviValue t1.locals) vars
            have corrPresent : ∀ key ∈ corr, sptLookup key t1.locals ≠ none := by
              intro key member absent
              have mapped := getVars_present corr (sptMap dataToBviValue t1.locals) env mappedReads key member
              simp [sptLookup_sptMap, absent] at mapped
            have present : ∀ key ∈ live ++ corr, sptLookup key t1.locals ≠ none := by
              intro key member
              rcases List.mem_append.mp member with liveMember | corrMember
              · exact livePresent key liveMember
              · exact corrPresent key corrMember
            let roots := namesOfList (live ++ corr)
            let saved := sptMkWf (sptInter t1.locals roots)
            have cut : DataSem.cutEnv roots t1.locals = some saved :=
              cutEnv_namesOfList (live ++ corr) t1.locals present
            let targetNext := DataSem.setVar n dataValue { t1 with locals := saved }
            refine ⟨targetNext, .force (some (n, roots)) location name, none, [n], max (n + 1) (name + 1), none, ?_, ?_, ?_, ?_⟩
            · simp [compileSource, nameAt, roots]
            · simp [DataSem.evaluate, dataRead, dataInspect, cut, targetNext, roots]
            · simpa [stateRel, DataSem.setVar, targetNext] using related
            · have outcome := forceValueOutcome t1 targetNext n corr live env dataValue vars fresh (by rfl) (by rfl) (by rfl)
              simpa [nextEq, dataProjected] using outcome
        | notEvaluated =>
          cases sourceCode : BvlSem.findCode (some location) [thunk, value] s1.code with
          | none =>
            simp [BviSem.evaluate, atIndex, inspect, sourceCode] at run
            obtain ⟨rfl, rfl⟩ := run
            exact False.elim (notTypeError rfl)
          | some pair =>
            obtain ⟨callArgs, body⟩ := pair
            have projectedCode : BvlSem.findCode (some location) ([dataThunk, dataValue].map dataToBviValue) s1.code =
                some (callArgs, body) := by simpa [projected, dataProjected] using sourceCode
            obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
              findCode_projection (some location) [dataThunk, dataValue] s1 t1 callArgs body related projectedCode
            by_cases zero : s1.clock = 0
            · have targetClock : t1.clock = 0 := by rw [← related.1, zero]
              simp [BviSem.evaluate, atIndex, inspect, sourceCode, zero] at run
              obtain ⟨rfl, rfl⟩ := run
              cases tail with
              | true =>
                let nextState := { t1 with stack := [], locals := .ln }
                refine ⟨nextState, .force none location name, some (.err (.abort .timeoutError)), [n], max (n + 1) (name + 1), none, ?_, ?_, ?_, ?_⟩
                · simp [compileSource, nameAt]
                · simp [DataSem.evaluate, dataRead, dataInspect, targetCode, targetClock, nextState]
                · simpa [stateRel, nextState, zero, targetClock] using related
                · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
              | false =>
                let roots := live ++ corr
                let saved := sptMkWf (sptInter t1.locals (namesOfList roots))
                have rootsPresent : ∀ key ∈ roots, sptLookup key t1.locals ≠ none := by
                  simpa [roots, DataSem.getVars] using
                    (roots_present t1 [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
                have cut : DataSem.cutEnv (namesOfList roots) t1.locals = some saved :=
                  cutEnv_namesOfList roots t1.locals rootsPresent
                let callState := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1))
                let nextState := { callState with stack := [], locals := .ln }
                refine ⟨nextState, .force (some (n, namesOfList roots)) location name,
                  some (.err (.abort .timeoutError)), [n], max (n + 1) (name + 1), none, ?_, ?_, ?_, ?_⟩
                · simp [compileSource, nameAt, roots]
                · simp [DataSem.evaluate, dataRead, dataInspect, targetCode, targetClock, cut, callState, nextState]
                · simpa [stateRel, nextState, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock,
                    zero, targetClock] using related
                · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
            · have calleeFacts : BviSem.evaluate [body] callArgs (BviSem.decClock 1 s1) = (res, s2) ∧ ¬isReturn res := by
                cases callRun : BviSem.evaluate [body] callArgs (BviSem.decClock 1 s1) with
                | mk outcome next =>
                  cases outcome with
                  | val values =>
                    simp [BviSem.evaluate, atIndex, inspect, sourceCode, zero, callRun] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact ⟨rfl, by simp [isReturn]⟩
                  | err error =>
                    cases error with
                    | abort reason =>
                      simp [BviSem.evaluate, atIndex, inspect, sourceCode, zero, callRun] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact ⟨rfl, by simp [isReturn]⟩
                    | raise raised =>
                      cases raised with
                      | exn value =>
                        simp [BviSem.evaluate, atIndex, inspect, sourceCode, zero, callRun] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact ⟨rfl, by simp [isReturn]⟩
                      | ret values =>
                        simp [BviSem.evaluate, atIndex, inspect, sourceCode, zero, callRun] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact False.elim (notTypeError rfl)
              have calleeNotType : res ≠ .err (.abort .typeError) := notTypeError
              subst callArgs
              have ih := calleeIH thunk value (dataArgs.map dataToBviValue) body atIndex inspect sourceCode zero
              cases tail with
              | true =>
                let entered := DataSem.callEnv dataArgs size (DataSem.decClock t1)
                have entryRel : stateRel (BviSem.decClock 1 s1) entered := by
                  simpa [entered, stateRel, DataSem.callEnv] using stateRel_decClock s1 t1 related
                have entryLocals : entered.locals = sptFromList dataArgs := rfl
                have entryJump : isException res → DataSem.jumpExc entered ≠ none := by
                  intro raised
                  cases oldJump : DataSem.jumpExc t1 with
                  | none => exact False.elim (exceptionJump raised oldJump)
                  | some jumped =>
                    have transported := DataSem.jumpExc_transport t1 entered jumped rfl rfl oldJump
                    rw [transported]
                    simp
                obtain ⟨targetNext, result, ls, targetRun, finalRel, calleeOutcome⟩ :=
                  compileCalleeFull body dataArgs (BviSem.decClock 1 s1) s2 entered res ih calleeFacts.1
                    calleeNotType entryRel entryLocals entryJump
                have projectedResult := calleeOutcome.1 calleeFacts.2
                have control := calleeOutcome.2.2.1
                have jumped := calleeOutcome.2.2.2.2
                have targetNonzero : t1.clock ≠ 0 := by simpa [← related.1] using zero
                refine ⟨targetNext, .force none location name, some result, [n], max (n + 1) (name + 1), ls, ?_, ?_, finalRel, ?_⟩
                · simp [compileSource, nameAt]
                · have run' : DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size (DataSem.decClock t1)) = (some result, targetNext) := by
                    simpa [entered] using targetRun
                  simp [DataSem.evaluate, dataRead, dataInspect, targetCode, targetNonzero, run']
                · simp only [correctOutcome]
                  refine ⟨fun _ => projectedResult, fun returned => False.elim (calleeFacts.2 returned), ?_, by simp, ?_⟩
                  · intro outcome
                    simpa [entered, DataSem.callEnv, DataSem.decClock] using control outcome
                  · intro raised
                    simpa [entered, DataSem.callEnv, DataSem.decClock] using jumped raised
              | false =>
                let roots := live ++ corr
                let saved := sptMkWf (sptInter t1.locals (namesOfList roots))
                have rootsPresent : ∀ key ∈ roots, sptLookup key t1.locals ≠ none := by
                  simpa [roots, DataSem.getVars] using
                    (roots_present t1 [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
                have cut : DataSem.cutEnv (namesOfList roots) t1.locals = some saved :=
                  cutEnv_namesOfList roots t1.locals rootsPresent
                let entered := DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1))
                have entryRel : stateRel (BviSem.decClock 1 s1) entered := by
                  simpa [entered, stateRel, DataSem.callEnv, DataSem.pushEnv] using stateRel_decClock s1 t1 related
                have entryLocals : entered.locals = sptFromList dataArgs := rfl
                have entryJump : isException res → DataSem.jumpExc entered ≠ none := by
                  intro raised
                  have original := exceptionJump raised
                  change DataSem.jumpExc (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1))) ≠ none
                  rw [DataSem.jumpExc_callEnv_push_noHandler]
                  cases jumpRun : DataSem.jumpExc t1 <;> simp_all
                obtain ⟨targetNext, result, ls, targetRun, finalRel, calleeOutcome⟩ :=
                  compileCalleeFull body dataArgs (BviSem.decClock 1 s1) s2 entered res ih calleeFacts.1
                    calleeNotType entryRel entryLocals entryJump
                have projectedResult := calleeOutcome.1 calleeFacts.2
                have control := calleeOutcome.2.2.1
                have jumped := calleeOutcome.2.2.2.2
                have targetNonzero : t1.clock ≠ 0 := by simpa [← related.1] using zero
                cases result with
                | val values =>
                  have resultEq : res = .val (values.map dataToBviValue) := by
                    simpa [dataToBviResult] using projectedResult.symm
                  have singleton := BviSem.evaluate_singleton body (dataArgs.map dataToBviValue)
                    (BviSem.decClock 1 s1) s2 (values.map dataToBviValue) (by simpa [resultEq] using calleeFacts.1)
                  obtain ⟨sourceValue, singleton⟩ := singleton
                  have lengthOne : values.length = 1 := by
                    have length := congrArg List.length singleton
                    simpa using length
                  cases values with
                  | nil => simp at lengthOne
                  | cons dataResult rest =>
                    cases rest with
                    | cons other more => simp at lengthOne
                    | nil =>
                      have sourceResult : res = .val [dataToBviValue dataResult] := by
                        simpa [dataToBviResult] using projectedResult.symm
                      subst res
                      have sourceIsResult : isResult (.val [dataToBviValue dataResult]) := ⟨_, rfl⟩
                      obtain ⟨stack, handler⟩ := control (Or.inl sourceIsResult)
                      have stackEq : targetNext.stack = .env t1.localsSize saved :: t1.stack := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using stack.symm
                      have handlerEq : targetNext.handler = t1.handler := by
                        simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using handler.symm
                      let restored := { targetNext with stack := t1.stack, locals := saved, localsSize := t1.localsSize }
                      have popRun : DataSem.popEnv targetNext = some restored := by
                        simp [DataSem.popEnv, stackEq, restored]
                      let final := DataSem.setVar n dataResult restored
                      have nameBelow : name < n := by
                        by_contra h
                        have absent := fresh name (by omega)
                        simp [lookup] at absent
                      have nextEq : max (n + 1) (name + 1) = n + 1 := by omega
                      have relFinal : stateRel s2 final := by
                        simpa [stateRel, final, restored, DataSem.setVar] using finalRel
                      have outcome := forceValueOutcome t1 final n corr live env dataResult vars fresh
                        (by rfl) (by rfl) (by simpa [final, restored, DataSem.setVar] using handlerEq)
                      refine ⟨final, .force (some (n, namesOfList roots)) location name, none, [n],
                        max (n + 1) (name + 1), none, ?_, ?_, relFinal, ?_⟩
                      · simp [compileSource, nameAt, roots]
                      · have run' : DataSem.evaluate (compileExp dataArgs.length body)
                            (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1))) =
                              (some (.val [dataResult]), targetNext) := by simpa [entered] using targetRun
                        have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1)))
                            ((some (.val [dataResult]) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                              ((some (.val [dataResult]) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                          rw [← run', DataSem.fixClock_evaluate]
                        simp [DataSem.evaluate, dataRead, dataInspect, targetCode, targetNonzero, cut, run', clamped, popRun, final]
                      · simpa [nextEq, dataToBviResult] using outcome
                | err error =>
                  cases error with
                  | abort reason =>
                    have sourceResult : res = .err (.abort reason) := by simpa [dataToBviResult] using projectedResult.symm
                    subst res
                    refine ⟨targetNext, .force (some (n, namesOfList roots)) location name,
                      some (.err (.abort reason)), [n], max (n + 1) (name + 1), ls, ?_, ?_, finalRel, ?_⟩
                    · simp [compileSource, nameAt, roots]
                    · have run' : DataSem.evaluate (compileExp dataArgs.length body)
                          (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1))) =
                            (some (.err (.abort reason)), targetNext) := by simpa [entered] using targetRun
                      have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1)))
                          ((some (.err (.abort reason)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                          ((some (.err (.abort reason)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                        rw [← run', DataSem.fixClock_evaluate]
                      simp [DataSem.evaluate, dataRead, dataInspect, targetCode, targetNonzero, cut, run', clamped]
                    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
                  | raise raised =>
                    have sourceResult : res = .err (.raise (.exn (dataToBviValue raised))) := by
                      simpa [dataToBviResult] using projectedResult.symm
                    subst res
                    have raisedResult : isException (.err (.raise (.exn (dataToBviValue raised)))) := ⟨_, rfl⟩
                    have calleeJump := jumped raisedResult
                    have jumpRun : DataSem.jumpExc { targetNext with stack := .env t1.localsSize saved :: t1.stack, handler := t1.handler } =
                        some { targetNext with localsSize := ls } := by
                      simpa [entered, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using calleeJump
                    have stripped := jumpExc_stripSaved t1 targetNext saved ls (exceptionJump raisedResult) jumpRun
                    refine ⟨targetNext, .force (some (n, namesOfList roots)) location name,
                      some (.err (.raise raised)), [n], max (n + 1) (name + 1), ls, ?_, ?_, finalRel, ?_⟩
                    · simp [compileSource, nameAt, roots]
                    · have run' : DataSem.evaluate (compileExp dataArgs.length body)
                          (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1))) =
                            (some (.err (.raise raised)), targetNext) := by simpa [entered] using targetRun
                      have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size (DataSem.pushEnv saved false (DataSem.decClock t1)))
                          ((some (.err (.raise raised)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) =
                            ((some (.err (.raise raised)) : Option (Result (List DataSem.Value) DataSem.Value)), targetNext) := by
                        rw [← run', DataSem.fixClock_evaluate]
                      simp [DataSem.evaluate, dataRead, dataInspect, targetCode, targetNonzero, cut, run', clamped]
                    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException, stripped]
end Flapjack.Compiler.Backend.BviToData
