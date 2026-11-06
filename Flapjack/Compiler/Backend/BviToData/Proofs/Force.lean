import Flapjack.Compiler.Backend.BviToData.Proofs.Install
import Flapjack.Compiler.Backend.BviToData.Proofs.Thunk
import Flapjack.Compiler.Backend.BviToData.Proofs.FindCode
import Flapjack.Compiler.Backend.BviToData.Proofs.Call
import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush

/-! Thunk forcing cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A source thunk selected from the environment has a corresponding data
local and an inspection result with the same mode and projected value. -/
theorem force_inspection_projection {C F : Type} (index : Nat) (env : List BvlSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F) (corr : List Nat)
    (thunk result : BvlSem.Value) (mode : AstHOL.ThunkMode)
    (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk mode result)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (related : stateRel source target) :
    ∃ name dataThunk dataValue, corr[index]? = some name ∧
      DataSem.getVar name target.locals = some dataThunk ∧ dataToBviValue dataThunk = thunk ∧
      DataSem.destThunk dataThunk target.refs = .isThunk mode dataValue ∧
      dataToBviValue dataValue = result := by
  obtain ⟨name, nameAt, valueAt⟩ :=
    DataProps.varCorr_lookup env corr (sptMap dataToBviValue target.locals) vars index thunk sourceVar
  simp only [DataSem.getVar, sptLookup_sptMap] at valueAt
  cases found : sptLookup name target.locals with
  | none => simp [found] at valueAt
  | some dataThunk =>
    simp only [found, Option.map_some, Option.some.injEq] at valueAt
    have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
      intro key
      rw [← sptLookup_sptMap]
      exact related.2.2.2.2.1 key
    have inspected := destThunk_projection dataThunk target.refs source.refs refs
    rw [valueAt, sourceThunk] at inspected
    cases inspect : DataSem.destThunk dataThunk target.refs with
    | badRef => simp [inspect, projectThunkResult] at inspected
    | notThunk => simp [inspect, projectThunkResult] at inspected
    | isThunk actual dataValue =>
      simp [inspect, projectThunkResult] at inspected
      obtain ⟨rfl, projected⟩ := inspected
      exact ⟨name, dataThunk, dataValue, nameAt, by simpa [DataSem.getVar] using found,
        valueAt, inspect, projected.symm⟩

/-- An unevaluated thunk with a valid code target times out on both sides
when the source clock is zero. This covers both return modes; recursive thunk
evaluation remains a separate case. -/
theorem simulationFor_force_timeout {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (thunk function : BvlSem.Value) (callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .notEvaluated function)
    (sourceCode : BvlSem.findCode (some label) [thunk, function] source.code = some (callArgs, body))
    (clock : source.clock = 0)
    (target : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (related : stateRel source target) (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none) :
    BviSem.evaluate [.force label index] env source = (.err (.abort .timeoutError), { source with clock := 0 }) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr tail live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel { source with clock := 0 } targetNext ∧
      correctOutcome (.err (.abort .timeoutError)) target targetNext n next corr live names env tail pres ls := by
  classical
  have sourceRun : BviSem.evaluate [.force label index] env source =
      (.err (.abort .timeoutError), { source with clock := 0 }) := by
    simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock]
  obtain ⟨name, dataThunk, dataFunction, nameAt, read, thunkProjection, inspect, functionProjection⟩ :=
    force_inspection_projection index env source target corr thunk function .notEvaluated sourceVar sourceThunk vars related
  have projectedCode : BvlSem.findCode (some label) ([dataThunk, dataFunction].map dataToBviValue) source.code =
      some (callArgs, body) := by simpa [thunkProjection, functionProjection] using sourceCode
  obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
    findCode_direct source target label [dataThunk, dataFunction] callArgs body related projectedCode
  have targetClock : target.clock = 0 := by rw [← related.1, clock]
  cases tail with
  | true =>
    let nextState := { target with stack := [], locals := .ln }
    refine ⟨sourceRun, nextState, .force none label name, some (.err (.abort .timeoutError)),
      [n], max (n + 1) (name + 1), none, ?_, ?_, ?_, ?_⟩
    · simp [compileSource, nameAt]
    · simp [DataSem.evaluate, read, inspect, targetCode, targetClock, nextState]
    · simpa [stateRel, nextState, clock, targetClock] using related
    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
  | false =>
    let roots := live ++ corr
    let cut := sptMkWf (sptInter target.locals (namesOfList roots))
    have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
      simpa [roots, DataSem.getVars] using
        (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
    have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
      cutEnv_namesOfList roots target.locals rootsPresent
    let callState := DataSem.callEnv dataArgs size (DataSem.pushEnv cut false (DataSem.decClock target))
    let nextState := { callState with stack := [], locals := .ln }
    refine ⟨sourceRun, nextState, .force (some (n, namesOfList roots)) label name,
      some (.err (.abort .timeoutError)), [n], max (n + 1) (name + 1), none, ?_, ?_, ?_, ?_⟩
    · simp [compileSource, nameAt, roots]
    · simp [DataSem.evaluate, read, inspect, targetCode, targetClock, cutEnv, callState, nextState]
    · simpa [stateRel, nextState, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock,
        clock, targetClock] using related
    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- Forcing an already evaluated thunk satisfies the expression simulation
in both tail positions. The unevaluated-thunk call case remains open, and
this case is untagged pending evaluator correspondence review. -/
theorem simulationFor_force_evaluated {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (thunk result : BvlSem.Value) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .evaluated result)
    (target : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (related : stateRel source target) (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none) :
    BviSem.evaluate [.force label index] env source = (.val [result], source) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr tail live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel source targetNext ∧
      correctOutcome (.val [result]) target targetNext n next corr live names env tail pres ls := by
  classical
  have sourceRun : BviSem.evaluate [.force label index] env source = (.val [result], source) := by
    simp [BviSem.evaluate, sourceVar, sourceThunk]
  obtain ⟨name, nameAt, valueAt⟩ :=
    DataProps.varCorr_lookup env corr (sptMap dataToBviValue target.locals) vars index thunk sourceVar
  simp only [DataSem.getVar, sptLookup_sptMap] at valueAt
  cases found : sptLookup name target.locals with
  | none => simp [found] at valueAt
  | some dataThunk =>
    simp only [found, Option.map_some, Option.some.injEq] at valueAt
    have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
      intro key
      rw [← sptLookup_sptMap]
      exact related.2.2.2.2.1 key
    have inspected := destThunk_projection dataThunk target.refs source.refs refs
    rw [valueAt, sourceThunk] at inspected
    cases inspect : DataSem.destThunk dataThunk target.refs with
    | badRef => simp [inspect, projectThunkResult] at inspected
    | notThunk => simp [inspect, projectThunkResult] at inspected
    | isThunk mode dataValue =>
      cases mode with
      | notEvaluated => simp [inspect, projectThunkResult] at inspected
      | evaluated =>
        simp [inspect, projectThunkResult] at inspected
        have projected : result = dataToBviValue dataValue := inspected
        have nameLt : name < n := by
          by_contra bound
          have absent := fresh name (by omega)
          rw [found] at absent
          contradiction
        have nextBound : max (n + 1) (name + 1) = n + 1 := Nat.max_eq_left (by omega)
        cases tail with
        | true =>
          refine ⟨sourceRun, DataSem.flushState false target, .force none label name, some (.val [dataValue]),
            [n], n + 1, none, ?_, ?_, ?_, ?_⟩
          · simp [compileSource, nameAt, nextBound]
          · simp [DataSem.evaluate, DataSem.getVar, found, inspect]
          · simpa [stateRel, DataSem.flushState] using related
          · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException,
              DataSem.flushState, ← projected]
        | false =>
          let roots := live ++ corr
          let cut := sptMkWf (sptInter target.locals (namesOfList roots))
          let targetNext := DataSem.setVar n dataValue { target with locals := cut }
          have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
            simpa [roots, DataSem.getVars] using
              (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
          have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
            cutEnv_namesOfList roots target.locals rootsPresent
          have execution : DataSem.evaluate (.force (some (n, namesOfList roots)) label name) target =
              (none, targetNext) := by
            simp [DataSem.evaluate, DataSem.getVar, found, inspect, cutEnv, targetNext]
          have finalRel : stateRel source targetNext := by
            simpa [targetNext, DataSem.setVar, stateRel] using related
          have locals : targetNext.locals = sptInsert n dataValue cut := by simp [targetNext, DataSem.setVar]
          have destRead : sptLookup n targetNext.locals = some dataValue := by
            simp [locals, sptLookup_sptInsert_same]
          have lookupOther : ∀ key, key ≠ n → sptLookup key targetNext.locals =
              if key ∈ roots then sptLookup key target.locals else none := by
            intro key different
            rw [locals, sptLookup_sptInsert_ne n key dataValue cut different]
            exact lookup_cut_namesOfList roots target.locals key
          have keeps : ∀ key ∈ roots, key ≠ n → sptLookup key targetNext.locals = sptLookup key target.locals := by
            intro key member different
            rw [lookupOther key different, if_pos member]
          have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
            apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
            intro key member
            have root : key ∈ roots := by simp [roots, member]
            have different : key ≠ n := by
              intro equal
              subst key
              exact rootsPresent n root (fresh n (Nat.le_refl n))
            exact keeps key root different
          refine ⟨sourceRun, targetNext, .force (some (n, namesOfList roots)) label name, none,
            [n], n + 1, none, ?_, execution, finalRel, ?_⟩
          · simp [compileSource, nameAt, nextBound, roots]
          · simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
            refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro key bound
              have different : key ≠ n := by omega
              rw [lookupOther key different]
              simp [fresh key (by omega)]
            · intro key v lookup
              by_cases equal : key = n
              · omega
              · have oldLookup : sptLookup key target.locals = some v := by
                  rw [lookupOther key equal] at lookup
                  split at lookup <;> simp_all
                by_contra bound
                have absent := fresh key (by omega)
                rw [oldLookup] at absent
                contradiction
            · intro key v lookup needed
              have different : key ≠ n := by
                intro equal
                subst key
                have absent := fresh n (Nat.le_refl n)
                rw [lookup] at absent
                contradiction
              have root : key ∈ roots := by
                by_cases member : key ∈ live
                · simp [roots, member]
                · simp [roots, needed member]
              rw [keeps key root different]
              exact lookup
            · rfl
            · rfl
            · intro available
              simpa [targetNext, DataSem.setVar, DataSem.jumpExc] using available
            · constructor
              · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
              · constructor

/-- A positive-clock tail force simulates a non-returning recursive thunk
body through the actual optimized function stored in the target code. The
body simulation is the recursive induction hypothesis. -/
theorem simulationFor_force_tail_recursive {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (thunk function : BvlSem.Value) (callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (res : BviSem.BviResult) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .notEvaluated function)
    (sourceCode : BvlSem.findCode (some label) [thunk, function] source.code = some (callArgs, body))
    (clock : source.clock ≠ 0)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock 1 source) = (res, nextSource))
    (notReturn : ¬ isReturn res) (notType : res ≠ .err (.abort .typeError))
    (ih : simulationFor [body] callArgs (BviSem.decClock 1 source))
    (target : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (related : stateRel source target)
    (exceptionJump : isException res → DataSem.jumpExc target ≠ none) :
    BviSem.evaluate [.force label index] env source = (res, nextSource) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr true live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel nextSource targetNext ∧
      correctOutcome res target targetNext n next corr live names env true pres ls := by
  have sourceRun : BviSem.evaluate [.force label index] env source = (res, nextSource) := by
    simp only [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock, ↓reduceIte, bodyRun]
    cases res with
    | val values => rfl
    | err error =>
      cases error with
      | abort error => rfl
      | raise value =>
        cases value with
        | exn value => rfl
        | ret values => exact False.elim (notReturn ⟨values, rfl⟩)
  obtain ⟨name, dataThunk, dataFunction, nameAt, read, thunkProjection, inspect, functionProjection⟩ :=
    force_inspection_projection index env source target corr thunk function .notEvaluated sourceVar sourceThunk vars related
  have projectedCode : BvlSem.findCode (some label) ([dataThunk, dataFunction].map dataToBviValue) source.code =
      some (callArgs, body) := by simpa [thunkProjection, functionProjection] using sourceCode
  obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
    findCode_direct source target label [dataThunk, dataFunction] callArgs body related projectedCode
  subst callArgs
  have targetClock : target.clock ≠ 0 := by simpa [← related.1] using clock
  have callJump : isException res → DataSem.jumpExc (DataSem.callEnv dataArgs size (DataSem.decClock target)) ≠ none := by
    intro exception
    have available := exceptionJump exception
    cases old : DataSem.jumpExc target with
    | none => exact False.elim (available old)
    | some jumped =>
      have moved := DataSem.jumpExc_transport target (DataSem.callEnv dataArgs size (DataSem.decClock target))
        jumped rfl rfl old
      rw [moved]
      simp
  obtain ⟨result, final, names, next, ls, localsSize, stackMax, safe, peak, bodyTarget,
      finalRel, optimizedRel, outcome⟩ :=
    compileExp_callEnv body dataArgs (BviSem.decClock 1 source) nextSource res (DataSem.decClock target) size
      ih bodyRun notType (stateRel_decClock source target related) callJump
  let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
  have optimizedOutcome := correctOutcome_some_resources res
    (DataSem.callEnv dataArgs size (DataSem.decClock target)) final dataArgs.length next
    (List.range dataArgs.length) [] names (dataArgs.map dataToBviValue) true result ls localsSize stackMax safe peak outcome
  have targetRun : DataSem.evaluate (.force none label name) target = (some result, optimized) := by
    simp [DataSem.evaluate, read, inspect, targetCode, targetClock, bodyTarget, optimized]
  refine ⟨sourceRun, optimized, .force none label name, some result, [n], max (n + 1) (name + 1), ls,
    ?_, targetRun, optimizedRel, ?_⟩
  · simp [compileSource, nameAt]
  · simpa [correctOutcome, DataSem.callEnv, DataSem.decClock, optimized] using optimizedOutcome

/-- A positive-clock non-tail force propagates a recursive thunk abort through
the saved caller frame. This is an evaluator case with the recursive body
simulation as its induction hypothesis. -/
theorem simulationFor_force_nontail_abort {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (thunk function : BvlSem.Value) (callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (error : Abort) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .notEvaluated function)
    (sourceCode : BvlSem.findCode (some label) [thunk, function] source.code = some (callArgs, body))
    (clock : source.clock ≠ 0)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock 1 source) = (.err (.abort error), nextSource))
    (notType : error ≠ .typeError)
    (ih : simulationFor [body] callArgs (BviSem.decClock 1 source))
    (target : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (related : stateRel source target) (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none) :
    BviSem.evaluate [.force label index] env source = (.err (.abort error), nextSource) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr false live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel nextSource targetNext ∧
      correctOutcome (.err (.abort error)) target targetNext n next corr live names env false pres ls := by
  have sourceRun : BviSem.evaluate [.force label index] env source = (.err (.abort error), nextSource) := by
    simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock, bodyRun]
  obtain ⟨name, dataThunk, dataFunction, nameAt, read, thunkProjection, inspect, functionProjection⟩ :=
    force_inspection_projection index env source target corr thunk function .notEvaluated sourceVar sourceThunk vars related
  have projectedCode : BvlSem.findCode (some label) ([dataThunk, dataFunction].map dataToBviValue) source.code =
      some (callArgs, body) := by simpa [thunkProjection, functionProjection] using sourceCode
  obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
    findCode_direct source target label [dataThunk, dataFunction] callArgs body related projectedCode
  subst callArgs
  have targetClock : target.clock ≠ 0 := by simpa [← related.1] using clock
  let roots := live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
    simpa [roots, DataSem.getVars] using
      (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
    cutEnv_namesOfList roots target.locals rootsPresent
  let pushed := DataSem.pushEnv cut false (DataSem.decClock target)
  have callRelated := stateRel_pushEnv (BviSem.decClock 1 source) (DataSem.decClock target) cut false
    (stateRel_decClock source target related)
  obtain ⟨result, final, names, next, ls, localsSize, stackMax, safe, peak, bodyTarget,
      finalRel, optimizedRel, outcome⟩ :=
    compileExp_callEnv body dataArgs (BviSem.decClock 1 source) nextSource (.err (.abort error)) pushed size
      ih bodyRun (by simpa using notType) callRelated (by simp [isException])
  have resultEq : result = .err (.abort error) := by
    have projected := outcome.1 (by simp [isReturn])
    cases result with
    | val values => simp [dataToBviResult] at projected
    | err failure =>
      cases failure with
      | abort reason => simpa [dataToBviResult] using projected
      | raise value => simp [dataToBviResult] at projected
  subst result
  let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
  have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
      (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
      (some (.err (.abort error)), optimized) := by
    rw [DataSem.fixClock_evaluate, bodyTarget]
  have targetRun : DataSem.evaluate (.force (some (n, namesOfList roots)) label name) target =
      (some (.err (.abort error)), optimized) := by
    simp only [DataSem.evaluate, read, inspect, targetCode, targetClock, cutEnv, ↓reduceIte]
    rw [clamped]
  refine ⟨sourceRun, optimized, .force (some (n, namesOfList roots)) label name,
    some (.err (.abort error)), [n], max (n + 1) (name + 1), ls, ?_, targetRun, optimizedRel, ?_⟩
  · simp [compileSource, nameAt, roots]
  · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- A positive-clock non-tail force propagates an exception from the
recursive thunk body through the caller's saved frame. -/
theorem simulationFor_force_nontail_exception {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (thunk function : BvlSem.Value) (callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (value : BvlSem.Value) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .notEvaluated function)
    (sourceCode : BvlSem.findCode (some label) [thunk, function] source.code = some (callArgs, body))
    (clock : source.clock ≠ 0)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock 1 source) = (.err (.raise (.exn value)), nextSource))
    (ih : simulationFor [body] callArgs (BviSem.decClock 1 source))
    (target : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (related : stateRel source target) (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (exceptionJump : DataSem.jumpExc target ≠ none) :
    BviSem.evaluate [.force label index] env source = (.err (.raise (.exn value)), nextSource) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr false live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel nextSource targetNext ∧
      correctOutcome (.err (.raise (.exn value))) target targetNext n next corr live names env false pres ls := by
  have sourceRun : BviSem.evaluate [.force label index] env source = (.err (.raise (.exn value)), nextSource) := by
    simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock, bodyRun]
  obtain ⟨name, dataThunk, dataFunction, nameAt, read, thunkProjection, inspect, functionProjection⟩ :=
    force_inspection_projection index env source target corr thunk function .notEvaluated sourceVar sourceThunk vars related
  have projectedCode : BvlSem.findCode (some label) ([dataThunk, dataFunction].map dataToBviValue) source.code =
      some (callArgs, body) := by simpa [thunkProjection, functionProjection] using sourceCode
  obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
    findCode_direct source target label [dataThunk, dataFunction] callArgs body related projectedCode
  subst callArgs
  have targetClock : target.clock ≠ 0 := by simpa [← related.1] using clock
  let roots := live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
    simpa [roots, DataSem.getVars] using
      (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
    cutEnv_namesOfList roots target.locals rootsPresent
  let pushed := DataSem.pushEnv cut false (DataSem.decClock target)
  have callRelated := stateRel_pushEnv (BviSem.decClock 1 source) (DataSem.decClock target) cut false
    (stateRel_decClock source target related)
  have callJump : DataSem.jumpExc (DataSem.callEnv dataArgs size pushed) ≠ none := by
    change DataSem.jumpExc (DataSem.callEnv dataArgs size (DataSem.pushEnv cut false (DataSem.decClock target))) ≠ none
    rw [DataSem.jumpExc_callEnv_push_noHandler]
    cases h : DataSem.jumpExc target with
    | none => exact False.elim (exceptionJump h)
    | some jumped => simp
  obtain ⟨result, final, names, next, ls, localsSize, stackMax, safe, peak, bodyTarget,
      finalRel, optimizedRel, outcome⟩ :=
    compileExp_callEnv body dataArgs (BviSem.decClock 1 source) nextSource (.err (.raise (.exn value))) pushed size
      ih bodyRun (by simp) callRelated (by intro _; exact callJump)
  have projected := outcome.1 (by simp [isReturn])
  rw [dataToBviResult_eq] at projected
  obtain ⟨dataValue, resultEq, projection⟩ := projected
  simp only [BviSem.ExnOrRet.exn.injEq] at projection
  subst result
  let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
  have optimizedOutcome := correctOutcome_some_resources (.err (.raise (.exn value)))
    (DataSem.callEnv dataArgs size pushed) final dataArgs.length next
    (List.range dataArgs.length) [] names (dataArgs.map dataToBviValue) true (.err (.raise dataValue))
    ls localsSize stackMax safe peak outcome
  have innerJump := optimizedOutcome.2.2.2.2 (by simp [isException])
  have savedJump : DataSem.jumpExc { optimized with stack := .env target.localsSize cut :: target.stack, handler := target.handler } =
      some { optimized with localsSize := ls } := by
    simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock, optimized] using innerJump
  have finalJump := jumpExc_remove_saved_frame target optimized cut ls savedJump
  have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
      (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
      (some (.err (.raise dataValue)), optimized) := by
    rw [DataSem.fixClock_evaluate, bodyTarget]
  have targetRun : DataSem.evaluate (.force (some (n, namesOfList roots)) label name) target =
      (some (.err (.raise dataValue)), optimized) := by
    simp only [DataSem.evaluate, read, inspect, targetCode, targetClock, cutEnv, ↓reduceIte]
    rw [clamped]
  refine ⟨sourceRun, optimized, .force (some (n, namesOfList roots)) label name,
    some (.err (.raise dataValue)), [n], max (n + 1) (name + 1), ls, ?_, targetRun, optimizedRel, ?_⟩
  · simp [compileSource, nameAt, roots]
  · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException, projection, finalJump]

/-- A positive-clock non-tail force restores the saved caller environment
when the recursive thunk body produces a value. -/
theorem simulationFor_force_nontail_value {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (thunk function : BvlSem.Value) (callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (value : BvlSem.Value) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .notEvaluated function)
    (sourceCode : BvlSem.findCode (some label) [thunk, function] source.code = some (callArgs, body))
    (clock : source.clock ≠ 0)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock 1 source) = (.val [value], nextSource))
    (ih : simulationFor [body] callArgs (BviSem.decClock 1 source))
    (target : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (related : stateRel source target) (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none) :
    BviSem.evaluate [.force label index] env source = (.val [value], nextSource) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr false live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel nextSource targetNext ∧
      correctOutcome (.val [value]) target targetNext n next corr live names env false pres ls := by
  have sourceRun : BviSem.evaluate [.force label index] env source = (.val [value], nextSource) := by
    simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock, bodyRun]
  obtain ⟨name, dataThunk, dataFunction, nameAt, read, thunkProjection, inspect, functionProjection⟩ :=
    force_inspection_projection index env source target corr thunk function .notEvaluated sourceVar sourceThunk vars related
  have nameLt : name < n := by
    by_contra bound
    have absent := fresh name (by omega)
    simp only [DataSem.getVar] at read
    rw [absent] at read
    contradiction
  have nextBound : max (n + 1) (name + 1) = n + 1 := Nat.max_eq_left (by omega)
  have projectedCode : BvlSem.findCode (some label) ([dataThunk, dataFunction].map dataToBviValue) source.code =
      some (callArgs, body) := by simpa [thunkProjection, functionProjection] using sourceCode
  obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
    findCode_direct source target label [dataThunk, dataFunction] callArgs body related projectedCode
  subst callArgs
  have targetClock : target.clock ≠ 0 := by simpa [← related.1] using clock
  let roots := live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
    simpa [roots, DataSem.getVars] using
      (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
    cutEnv_namesOfList roots target.locals rootsPresent
  let pushed := DataSem.pushEnv cut false (DataSem.decClock target)
  have callRelated := stateRel_pushEnv (BviSem.decClock 1 source) (DataSem.decClock target) cut false
    (stateRel_decClock source target related)
  obtain ⟨result, final, names, next, ls, localsSize, stackMax, safe, peak, bodyTarget,
      finalRel, optimizedRel, outcome⟩ :=
    compileExp_callEnv body dataArgs (BviSem.decClock 1 source) nextSource (.val [value]) pushed size
      ih bodyRun (by simp) callRelated (by simp [isException])
  obtain ⟨dataValue, resultEq, projected⟩ : ∃ dataValue, result = .val [dataValue] ∧ dataToBviValue dataValue = value := by
    have projection := outcome.1 (by simp [isReturn])
    cases result with
    | err error => cases error <;> simp [dataToBviResult] at projection
    | val values =>
      cases values with
      | nil => simp [dataToBviResult] at projection
      | cons head tail =>
        cases tail with
        | nil => exact ⟨head, rfl, by simpa [dataToBviResult] using projection⟩
        | cons second rest => simp [dataToBviResult] at projection
  subst result
  have control := outcome.2.2.1 (by simp [isResult])
  have stack : final.stack = .env target.localsSize cut :: target.stack := by
    simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock] using control.1.symm
  have handler : final.handler = target.handler := by
    simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock] using control.2.symm
  let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
  let restored := { optimized with stack := target.stack, locals := cut, localsSize := target.localsSize }
  let targetNext := DataSem.setVar n dataValue restored
  have pop : DataSem.popEnv optimized = some restored := by
    simp [DataSem.popEnv, optimized, stack, restored]
  have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
      (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
      (some (.val [dataValue]), optimized) := by
    rw [DataSem.fixClock_evaluate, bodyTarget]
  have targetRun : DataSem.evaluate (.force (some (n, namesOfList roots)) label name) target = (none, targetNext) := by
    simp only [DataSem.evaluate, read, inspect, targetCode, targetClock, cutEnv, ↓reduceIte]
    rw [clamped, pop]
  have targetRel : stateRel nextSource targetNext := by
    simpa [targetNext, restored, DataSem.setVar, stateRel, optimized] using optimizedRel
  have locals : targetNext.locals = sptInsert n dataValue cut := by simp [targetNext, restored, DataSem.setVar]
  have destRead : sptLookup n targetNext.locals = some dataValue := by simp [locals, sptLookup_sptInsert_same]
  have lookupOther : ∀ key, key ≠ n → sptLookup key targetNext.locals =
      if key ∈ roots then sptLookup key target.locals else none := by
    intro key different
    rw [locals, sptLookup_sptInsert_ne n key dataValue cut different]
    exact lookup_cut_namesOfList roots target.locals key
  have keeps : ∀ key ∈ roots, key ≠ n → sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different, if_pos member]
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ roots := by simp [roots, member]
    have different : key ≠ n := by
      intro equal
      subst key
      exact rootsPresent n root (fresh n (Nat.le_refl n))
    exact keeps key root different
  refine ⟨sourceRun, targetNext, .force (some (n, namesOfList roots)) label name, none,
    [n], n + 1, none, ?_, targetRun, targetRel, ?_⟩
  · simp [compileSource, nameAt, nextBound, roots]
  · simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
    refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro key bound
      have different : key ≠ n := by omega
      rw [lookupOther key different]
      simp [fresh key (by omega)]
    · intro key v lookup
      by_cases equal : key = n
      · omega
      · have oldLookup : sptLookup key target.locals = some v := by
          rw [lookupOther key equal] at lookup
          split at lookup <;> simp_all
        by_contra bound
        have absent := fresh key (by omega)
        rw [oldLookup] at absent
        contradiction
    · intro key v lookup needed
      have different : key ≠ n := by
        intro equal
        subst key
        have absent := fresh n (Nat.le_refl n)
        rw [lookup] at absent
        contradiction
      have root : key ∈ roots := by
        by_cases member : key ∈ live
        · simp [roots, member]
        · simp [roots, needed member]
      rw [keeps key root different]
      exact lookup
    · simp [targetNext, restored, DataSem.setVar]
    · simp [targetNext, restored, DataSem.setVar, optimized, handler]
    · intro available
      cases old : DataSem.jumpExc target with
      | none => exact False.elim (available old)
      | some jumped =>
        have moved := DataSem.jumpExc_transport target targetNext jumped
          (by simp [targetNext, restored, DataSem.setVar])
          (by simp [targetNext, restored, DataSem.setVar, optimized, handler]) old
        rw [moved]
        simp
    · constructor
      · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
      · constructor

/-- An already evaluated thunk satisfies the complete compiler simulation
invariant at any clock. The evaluator and carrier correspondence still need
review against HOL, so this assembling lemma is untagged. -/
theorem simulationFor_force_of_evaluated {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (thunk value : BvlSem.Value) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .evaluated value) :
    simulationFor [.force label index] env source := by
  intro res s2 target n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  obtain ⟨sourceRun, targetNext, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩ :=
    simulationFor_force_evaluated label index env source thunk value sourceVar sourceThunk
      target n corr tail live vars fresh related livePresent
  rw [sourceRun] at run
  cases run
  exact ⟨targetNext, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩

/-- At zero clock, all non-type-error forcing executions are covered: an
already evaluated thunk returns its value, while a valid unevaluated thunk
times out. This assembles the cases into the compiler simulation invariant;
it remains untagged pending evaluator and carrier review. -/
theorem simulationFor_force_clock_zero {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (clock : source.clock = 0) : simulationFor [.force label index] env source := by
  intro res s2 target n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  cases sourceVar : env[index]? with
  | none =>
    simp [BviSem.evaluate, sourceVar] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notTypeError rfl)
  | some thunk =>
    cases sourceThunk : BviSem.destThunk thunk source.refs with
    | badRef =>
      simp [BviSem.evaluate, sourceVar, sourceThunk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notTypeError rfl)
    | notThunk =>
      simp [BviSem.evaluate, sourceVar, sourceThunk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notTypeError rfl)
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        obtain ⟨sourceRun, targetNext, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩ :=
          simulationFor_force_evaluated label index env source thunk value sourceVar sourceThunk
            target n corr tail live vars fresh related livePresent
        rw [sourceRun] at run
        cases run
        exact ⟨targetNext, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩
      | notEvaluated =>
        cases sourceCode : BvlSem.findCode (some label) [thunk, value] source.code with
        | none =>
          simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notTypeError rfl)
        | some pair =>
          obtain ⟨callArgs, body⟩ := pair
          obtain ⟨sourceRun, targetNext, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩ :=
            simulationFor_force_timeout label index env source thunk value callArgs body
              sourceVar sourceThunk sourceCode clock target n corr tail live vars related livePresent
          rw [sourceRun] at run
          cases run
          exact ⟨targetNext, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩

/-- The complete force-expression simulation, assuming the evaluator's
recursive induction hypothesis for any called thunk body. The assembled case
remains untagged pending HOL evaluator and state-carrier review. -/
theorem simulationFor_force {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (ih : ∀ thunk function callArgs body,
      env[index]? = some thunk →
      BviSem.destThunk thunk source.refs = .isThunk .notEvaluated function →
      BvlSem.findCode (some label) [thunk, function] source.code = some (callArgs, body) →
      source.clock ≠ 0 → simulationFor [body] callArgs (BviSem.decClock 1 source)) :
    simulationFor [.force label index] env source := by
  by_cases clock : source.clock = 0
  · exact simulationFor_force_clock_zero label index env source clock
  intro res s2 target n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  cases sourceVar : env[index]? with
  | none =>
    simp [BviSem.evaluate, sourceVar] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notTypeError rfl)
  | some thunk =>
    cases sourceThunk : BviSem.destThunk thunk source.refs with
    | badRef =>
      simp [BviSem.evaluate, sourceVar, sourceThunk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notTypeError rfl)
    | notThunk =>
      simp [BviSem.evaluate, sourceVar, sourceThunk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notTypeError rfl)
    | isThunk mode function =>
      cases mode with
      | evaluated =>
        exact simulationFor_force_of_evaluated label index env source thunk function sourceVar sourceThunk
          res s2 target n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
      | notEvaluated =>
        cases sourceCode : BvlSem.findCode (some label) [thunk, function] source.code with
        | none =>
          simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notTypeError rfl)
        | some pair =>
          obtain ⟨callArgs, body⟩ := pair
          generalize bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock 1 source) = bodyPair
          obtain ⟨bodyResult, nextSource⟩ := bodyPair
          by_cases returns : isReturn bodyResult
          · obtain ⟨values, rfl⟩ := returns
            simp [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock, bodyRun] at run
            obtain ⟨rfl, rfl⟩ := run
            exact False.elim (notTypeError rfl)
          · have whole : BviSem.evaluate [.force label index] env source = (bodyResult, nextSource) := by
              simp only [BviSem.evaluate, sourceVar, sourceThunk, sourceCode, clock, ↓reduceIte, bodyRun]
              cases bodyResult with
              | val values => rfl
              | err error =>
                cases error with
                | abort error => rfl
                | raise value =>
                  cases value with
                  | exn value => rfl
                  | ret values => exact False.elim (returns ⟨values, rfl⟩)
            rw [whole] at run
            cases run
            have bodyIH := ih thunk function callArgs body sourceVar sourceThunk sourceCode clock
            cases tail with
            | true =>
              exact (simulationFor_force_tail_recursive label index env source s2 thunk function
                callArgs body res sourceVar sourceThunk sourceCode clock bodyRun returns notTypeError bodyIH
                target n corr live vars related exceptionJump).2
            | false =>
              cases res with
              | val values =>
                obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton body callArgs (BviSem.decClock 1 source) s2 values bodyRun
                exact (simulationFor_force_nontail_value label index env source s2 thunk function
                  callArgs body value sourceVar sourceThunk sourceCode clock bodyRun bodyIH
                  target n corr live vars fresh related livePresent).2
              | err error =>
                cases error with
                | abort error =>
                  exact (simulationFor_force_nontail_abort label index env source s2 thunk function
                    callArgs body error sourceVar sourceThunk sourceCode clock bodyRun
                    (by simpa using notTypeError) bodyIH target n corr live vars related livePresent).2
                | raise value =>
                  cases value with
                  | exn value =>
                    exact (simulationFor_force_nontail_exception label index env source s2 thunk function
                      callArgs body value sourceVar sourceThunk sourceCode clock bodyRun bodyIH
                      target n corr live vars related livePresent (exceptionJump (by simp [isException]))).2
                  | ret values => exact False.elim (returns ⟨values, rfl⟩)

end Flapjack.Compiler.Backend.BviToData
