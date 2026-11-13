module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
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

private theorem varCorr_fromList {α β : Type} (f : α → β) (values : List α) :
    DataProps.varCorr (values.map f) (List.range values.length) (sptMap f (sptFromList values)) := by
  apply List.forall₂_iff_get.mpr
  constructor
  · simp
  · intro index leftBound rightBound
    have bound : index < values.length := by simpa using rightBound
    simp [DataSem.getVar, sptLookup_sptMap, sptLookupFromList_getElem?, bound]

private theorem forceValueOutcome {C F : Type} (target next : DataSem.State C F)
    (n : Nat) (corr live : List Nat) (env : List BvlSem.Value) (value : DataSem.Value)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k target.locals = none)
    (locals : next.locals = sptInsert n value (sptMkWf (sptInter target.locals (namesOfList (live ++ corr)))))
    (stack : next.stack = target.stack) (handler : next.handler = target.handler) :
    correctOutcome (.val [dataToBviValue value]) target next n (n + 1) corr live [n] env false none none := by
  have mappedReads := DataProps.getVars_thm corr env (sptMap dataToBviValue target.locals) vars
  have corrPresent : ∀ key ∈ corr, sptLookup key target.locals ≠ none := by
    intro key member absent
    have mapped := getVars_present corr (sptMap dataToBviValue target.locals) env mappedReads key member
    simp [sptLookup_sptMap, absent] at mapped
  let saved := sptMkWf (sptInter target.locals (namesOfList (live ++ corr)))
  have sameLocals : next.locals = sptInsert n value saved := locals
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, stack.symm, handler.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ n := by omega
    rw [sameLocals, sptLookup_sptInsert_ne n key value saved different]
    simp [saved, lookup_cut_namesOfList, fresh key (by omega)]
  · rw [sameLocals]
    apply varCorr_of_lookup_eq dataToBviValue target.locals (sptInsert n value saved) corr env vars
    intro key member
    have different : key ≠ n := by
      intro same
      subst key
      exact corrPresent n member (fresh n (Nat.le_refl n))
    rw [sptLookup_sptInsert_ne n key value saved different]
    simp [saved, lookup_cut_namesOfList, member]
  · intro key dataValue found
    rw [sameLocals] at found
    by_cases same : key = n
    · omega
    · rw [sptLookup_sptInsert_ne n key value saved same] at found
      by_contra bound
      have absent := fresh key (by omega)
      simp [saved, lookup_cut_namesOfList, absent] at found
  · intro key dataValue found needed
    have different : key ≠ n := by
      intro same
      subst key
      have absent := fresh n (Nat.le_refl n)
      rw [found] at absent
      contradiction
    rw [sameLocals, sptLookup_sptInsert_ne n key value saved different]
    have kept : key ∈ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    simpa [saved, lookup_cut_namesOfList, kept] using found
  · intro available
    cases run : DataSem.jumpExc target with
    | none => exact False.elim (available run)
    | some jumped =>
      have transported := DataSem.jumpExc_transport target next jumped stack handler run
      rw [transported]
      simp
  · rw [sameLocals]
    constructor
    · simp [DataSem.getVar, sptLookup_sptMap, sptLookup_sptInsert_same]
    · constructor

private theorem compileCallee {C F : Type} (body : Bvi.Exp) (args : List DataSem.Value)
    (source sourceNext : BviSem.BviState C F) (target : DataSem.State C F)
    (res : BviSem.BviResult)
    (ih : simulationFor [body] (args.map dataToBviValue) source)
    (run : BviSem.evaluate [body] (args.map dataToBviValue) source = (res, sourceNext))
    (notType : res ≠ .err (.abort .typeError)) (notReturn : ¬isReturn res)
    (related : stateRel source target) (locals : target.locals = sptFromList args)
    (jump : isException res → DataSem.jumpExc target ≠ none) :
    ∃ targetNext result ls,
      DataSem.evaluate (compileExp args.length body) target = (some result, targetNext) ∧
      stateRel sourceNext targetNext ∧ dataToBviResult result = res ∧
      ((isResult res ∨ isReturn res) → target.stack = targetNext.stack ∧ target.handler = targetNext.handler) ∧
      (isException res → DataSem.jumpExc { targetNext with stack := target.stack, handler := target.handler } =
        some { targetNext with localsSize := ls }) := by
  have vars : DataProps.varCorr (args.map dataToBviValue) (List.range args.length)
      (sptMap dataToBviValue target.locals) := by rw [locals]; exact varCorr_fromList dataToBviValue args
  have fresh : ∀ k, args.length ≤ k → sptLookup k target.locals = none := by
    intro k bound
    rw [locals, sptLookupFromList_getElem?]
    simp [Nat.not_lt.mpr bound]
  obtain ⟨next, prog, pres, vs, nextVar, ls, compiled, targetRun, finalRel, outcome⟩ :=
    ih res sourceNext target args.length (List.range args.length) true [] run notType vars (by simp) fresh related (by simp) jump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    have projected : dataToBviResult result = res := outcome.1 notReturn
    have allowed : (DataSem.evaluate prog target).1 ≠ some (.err (.abort .typeError)) := by
      rw [targetRun]
      intro bad
      have badResult : result = .err (.abort .typeError) := Option.some.inj bad
      subst result
      exact notType (by simpa [dataToBviResult] using projected.symm)
    have stopped : (DataSem.evaluate prog target).1 ≠ none := by simp [targetRun]
    obtain ⟨safe, peak, smx, lsz, optimized⟩ := optimise_correct prog target allowed stopped
    let final := { next with localsSize := lsz, safeForSpace := safe, peakHeapLength := peak, stackMax := smx }
    have optimizedRun : DataSem.evaluate (compileExp args.length body) target = (some result, final) := by
      simpa [compileExp, compiled, targetRun, final] using optimized
    refine ⟨final, result, ls, optimizedRun, ?_, projected, ?_, ?_⟩
    · exact (stateRel_peakSafe sourceNext next safe peak lsz smx).mp finalRel
    · intro isResult
      have old := outcome.2.2.1 isResult
      simpa [final] using old
    · intro isException
      have old := outcome.2.2.2.2 isException
      have changed := jumpExc_peakSafe { next with stack := target.stack, handler := target.handler }
        { next with localsSize := ls } safe peak lsz smx old
      simpa [final] using changed


private theorem jumpExc_stripSaved {C F : Type} (caller state : DataSem.State C F)
    (env : Spt DataSem.Value) (ls : Option Nat) (available : DataSem.jumpExc caller ≠ none)
    (run : DataSem.jumpExc { state with stack := .env caller.localsSize env :: caller.stack, handler := caller.handler } =
      some { state with localsSize := ls }) :
    DataSem.jumpExc { state with stack := caller.stack, handler := caller.handler } = some { state with localsSize := ls } := by
  have inside : caller.handler < caller.stack.length := by
    by_contra h
    apply available
    simp [DataSem.jumpExc, h]
  have shifted : caller.handler < (DataSem.Stack.env caller.localsSize env :: caller.stack).length := by simp; omega
  have offset : (DataSem.Stack.env caller.localsSize env :: caller.stack).length - (caller.handler + 1) =
      (caller.stack.length - (caller.handler + 1)) + 1 := by simp; omega
  have offset' : caller.stack.length - caller.handler =
      (caller.stack.length - (caller.handler + 1)) + 1 := by omega
  have insideLe : caller.handler ≤ caller.stack.length := Nat.le_of_lt inside
  simpa [DataSem.jumpExc, inside, insideLe, shifted, offset, offset', List.drop_succ_cons] using run

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
                obtain ⟨targetNext, result, ls, targetRun, finalRel, projectedResult, control, jumped⟩ :=
                  compileCallee body dataArgs (BviSem.decClock 1 s1) s2 entered res ih calleeFacts.1
                    calleeNotType calleeFacts.2 entryRel entryLocals entryJump
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
                obtain ⟨targetNext, result, ls, targetRun, finalRel, projectedResult, control, jumped⟩ :=
                  compileCallee body dataArgs (BviSem.decClock 1 s1) s2 entered res ih calleeFacts.1
                    calleeNotType calleeFacts.2 entryRel entryLocals entryJump
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
