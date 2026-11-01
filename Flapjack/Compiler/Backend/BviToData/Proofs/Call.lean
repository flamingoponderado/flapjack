import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.BviToData.Proofs.Optimise
import Flapjack.Compiler.Backend.BviToData.Proofs.FindCode
import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
import Flapjack.Compiler.Backend.Semantics.DataProps.Ticks
import Mathlib.Data.List.Induction

/-! Call argument cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem fromListFoldIndex {α : Type} (values : List α) (start : Nat) (tree : Spt α) :
    (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 1, sptInsert acc.1 value acc.2))
      (start, tree)).1 = start + values.length := by
  induction values generalizing start tree with
  | nil => simp
  | cons value values ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    omega

private theorem lookupFromList {α : Type} (values : List α) (key : Nat) :
    sptLookup key (sptFromList values) = values[key]? := by
  induction values using List.reverseRecOn with
  | nil => simp [sptFromList]
  | append_singleton values value ih =>
    have inserted : sptFromList (values ++ [value]) =
        sptInsert values.length value (sptFromList values) := by
      simp only [sptFromList, List.foldl_append, List.foldl_cons, List.foldl_nil,
        fromListFoldIndex, Nat.zero_add]
    rw [inserted]
    by_cases equal : key = values.length
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne values.length key value (sptFromList values) equal, ih]
      by_cases bound : key < values.length
      · simp [List.getElem?_append, bound]
      · have beyond : values.length < key := by omega
        simp [List.getElem?_append, bound, List.getElem?_eq_none, show 1 ≤ key - values.length by omega]

/-- Entering a data call gives each projected argument its corresponding
zero-based local name and leaves every later local absent. -/
theorem callEnv_argument_locals {C F : Type} (args : List DataSem.Value)
    (size : Option Nat) (target : DataSem.State C F) :
    DataProps.varCorr (args.map dataToBviValue) (List.range args.length)
      (sptMap dataToBviValue (DataSem.callEnv args size target).locals) ∧
    (∀ key, args.length ≤ key → sptLookup key (DataSem.callEnv args size target).locals = none) := by
  constructor
  · apply List.forall₂_iff_get.mpr
    constructor
    · simp
    · intro index leftBound rightBound
      have bound : index < args.length := by simpa using leftBound
      simp [DataSem.getVar, DataSem.callEnv, sptLookup_sptMap,
        lookupFromList, List.getElem?_eq_getElem bound]
  · intro key bound
    simp [DataSem.callEnv, lookupFromList, List.getElem?_eq_none bound]

/-- Entering a call does not change any field observed by the BVI/data state
relation. -/
theorem stateRel_callEnv {C F : Type} (source : BviSem.BviState C F)
    (target : DataSem.State C F) (args : List DataSem.Value) (size : Option Nat)
    (related : stateRel source target) : stateRel source (DataSem.callEnv args size target) := by
  simpa [stateRel, DataSem.callEnv] using related

/-- Saving a caller frame does not change any field observed by the BVI/data
state relation. -/
theorem stateRel_pushEnv {C F : Type} (source : BviSem.BviState C F)
    (target : DataSem.State C F) (env : Spt DataSem.Value) (handler : Bool)
    (related : stateRel source target) : stateRel source (DataSem.pushEnv env handler target) := by
  simpa [stateRel, DataSem.pushEnv] using related

/-- The generated ticks followed by call entry consume the same clock as a
BVI call and preserve the remaining state relation. -/
theorem stateRel_callEntry {C F : Type} (source : BviSem.BviState C F)
    (target : DataSem.State C F) (args : List DataSem.Value) (size : Option Nat) (ticks : Nat)
    (related : stateRel source target) :
    stateRel (BviSem.decClock (ticks + 1) source)
      (DataSem.callEnv args size (DataSem.decClock { target with clock := target.clock - ticks })) := by
  apply stateRel_callEnv
  rcases related with ⟨clocks, rest⟩
  refine ⟨?_, rest⟩
  simp only [BviSem.decClock, DataSem.decClock]
  rw [clocks]
  omega

/-- Run an optimized compiled function body from a freshly populated call
environment, given the recursive source simulation. The remaining exception
premise is the caller's actual handler obligation. -/
theorem compileExp_callEnv {C F : Type} (body : Bvi.Exp) (args : List DataSem.Value)
    (source nextSource : BviSem.BviState C F) (res : BviSem.BviResult)
    (target : DataSem.State C F) (size : Option Nat)
    (ih : simulationFor [body] (args.map dataToBviValue) source)
    (run : BviSem.evaluate [body] (args.map dataToBviValue) source = (res, nextSource))
    (notType : res ≠ .err (.abort .typeError)) (related : stateRel source target)
    (exceptionJump : isException res → DataSem.jumpExc (DataSem.callEnv args size target) ≠ none) :
    ∃ result final names next ls localsSize stackMax safe peak,
      DataSem.evaluate (compileExp args.length body) (DataSem.callEnv args size target) =
        (some result, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) ∧
      stateRel nextSource final ∧
      stateRel nextSource { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak } ∧
      correctOutcome res (DataSem.callEnv args size target) final args.length next
        (List.range args.length) [] names (args.map dataToBviValue) true (some result) ls := by
  obtain ⟨vars, fresh⟩ := callEnv_argument_locals args size target
  have callRelated := stateRel_callEnv source target args size related
  simpa using compileExp_of_simulation body (args.map dataToBviValue) source nextSource res
    (DataSem.callEnv args size target) ih run notType (by simpa using vars)
    (by simpa using fresh) callRelated exceptionJump

/-- An indirect call with a handler is rejected before evaluating its
arguments, so it has no non-type-error execution. -/
theorem simulationFor_call_invalid_handler {C F : Type} (ticks : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List BvlSem.Value) (state : BviSem.BviState C F) :
    simulationFor [.call ticks none args (some handler)] env state := by
  intro res next target n corr tail live run notTypeError
  simp [BviSem.evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact False.elim (notTypeError rfl)

/-- Successful call arguments followed by exhaustion within the generated
ticks produce the same timeout and related state on both sides. This is one
case of the unhandled-call simulation. -/
theorem simulationFor_call_ticksTimeout {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (timeout : smid.clock < ticks)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show smid.clock < ticks + 1 by omega]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    let rest := DataLang.mkTicks ticks (.call (if tail then none else some ([n1], namesOfList (live ++ corr))) dest argNames none)
    let last := { tmid with clock := 0, locals := .ln, stack := [], localsSize := some 0 }
    have targetTimeout : tmid.clock < ticks := by simpa [← middleRel.1] using timeout
    have restRun : DataSem.evaluate rest tmid = (some (.err (.abort .timeoutError)), last) := by
      simp [rest, DataSem.evaluate_mkTicks, targetTimeout, last]
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some (.err (.abort .timeoutError)), last) :=
      evaluateSeq_continue argsProg rest t1 tmid _ target targetBound restRun
    have finalRel : stateRel { smid with clock := 0 } last := by
      simpa [stateRel, last] using middleRel.2
    refine ⟨wholeRun, last, .seq argsProg rest, some (.err (.abort .timeoutError)), [n1], n1 + 1,
      ls, ?_, targetRun, finalRel, ?_⟩
    · simp [compileSource, compiled, rest]
    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- If generated ticks consume exactly the remaining clock, the call itself
times out. Both tail and returning calls preserve the BVI/data relation. -/
theorem simulationFor_call_entryTimeout {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (timeout : smid.clock = ticks)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, timeout]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, _, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedCode : BvlSem.findCode dest (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
      simpa [← projected] using sourceCode
    obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
      findCode_projection dest dataValues smid tmid callArgs body middleRel projectedCode
    have targetClock : tmid.clock = ticks := by simpa [← middleRel.1] using timeout
    let afterTicks := { tmid with clock := tmid.clock - ticks }
    have afterClock : afterTicks.clock = 0 := by simp [afterTicks, targetClock]
    have afterRead : DataSem.getVars argNames afterTicks.locals = some dataValues := by simpa [afterTicks] using read
    have afterCode : DataSem.findCode dest dataValues afterTicks.code afterTicks.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by simpa [afterTicks] using targetCode
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    cases tail with
    | true =>
      let call := DataLang.Prog.call none dest argNames none
      let last := DataSem.flushState true afterTicks
      have callRun : DataSem.evaluate call afterTicks = (some (.err (.abort .timeoutError)), last) := by
        simp [call, DataSem.evaluate, afterRead, afterCode, afterClock, last]
      have ticksRun : DataSem.evaluate (DataLang.mkTicks ticks call) tmid = (some (.err (.abort .timeoutError)), last) := by
        rw [DataSem.evaluate_mkTicks]
        rw [if_neg (by omega : ¬ tmid.clock < ticks)]
        exact callRun
      have targetRun := evaluateSeq_continue argsProg (DataLang.mkTicks ticks call) t1 tmid _ target targetBound ticksRun
      have finalRel : stateRel { smid with clock := 0 } last := by
        simpa [stateRel, last, DataSem.flushState, afterTicks, targetClock] using middleRel.2
      refine ⟨wholeRun, last, .seq argsProg (DataLang.mkTicks ticks call), some (.err (.abort .timeoutError)),
        [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, call]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
    | false =>
      let roots := live ++ corr
      let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
      have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
        simpa [roots, DataSem.getVars] using
          (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
      have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
        cutEnv_namesOfList roots tmid.locals rootsPresent
      let call := DataLang.Prog.call (some ([n1], namesOfList roots)) dest argNames none
      let callState := DataSem.callEnv dataArgs size (DataSem.pushEnv cut false (DataSem.decClock afterTicks))
      let last := { callState with stack := [], locals := .ln }
      have callRun : DataSem.evaluate call afterTicks = (some (.err (.abort .timeoutError)), last) := by
        simp [call, DataSem.evaluate, afterRead, afterCode, afterClock, cutEnv, callState, last]
      have ticksRun : DataSem.evaluate (DataLang.mkTicks ticks call) tmid = (some (.err (.abort .timeoutError)), last) := by
        rw [DataSem.evaluate_mkTicks]
        rw [if_neg (by omega : ¬ tmid.clock < ticks)]
        exact callRun
      have targetRun := evaluateSeq_continue argsProg (DataLang.mkTicks ticks call) t1 tmid _ target targetBound ticksRun
      have finalRel : stateRel { smid with clock := 0 } last := by
        simpa [stateRel, last, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, afterTicks, targetClock] using middleRel.2
      refine ⟨wholeRun, last, .seq argsProg (DataLang.mkTicks ticks call), some (.err (.abort .timeoutError)),
        [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, call, roots]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- All call timeouts after successful arguments and code lookup, including
the boundary at which the generated ticks consume the entire clock. -/
theorem simulationFor_call_timeout {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (timeout : smid.clock < ticks + 1)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  by_cases before : smid.clock < ticks
  · exact simulationFor_call_ticksTimeout ticks dest args env values callArgs body s1 smid ih
      argsRun sourceCode before t1 n corr tail live vars fresh related livePresent
  · exact simulationFor_call_entryTimeout ticks dest args env values callArgs body s1 smid ih
      argsRun sourceCode (by omega) t1 n corr tail live vars fresh related livePresent

/-- A tail call with sufficient clock runs the compiled callee. The callee
simulation is the evaluator's recursive induction hypothesis. -/
theorem simulationFor_call_tail_recursive {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid s2 : BviSem.BviState C F) (res : BviSem.BviResult)
    (ihArgs : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (clock : ticks + 1 ≤ smid.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (res, s2))
    (notReturn : ¬ isReturn res) (notType : res ≠ .err (.abort .typeError))
    (ihBody : simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid))
    (t1 : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException res → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (res, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr true live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome res t1 t2 n next corr live names env true pres ls := by
  have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
      (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (res, s2) := by
    rw [BviSem.fixClock_evaluate, bodyRun]
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 = (res, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, sourceCode,
      show ¬ smid.clock < ticks + 1 by omega, bodyClamped]
    cases res with
    | val values => rfl
    | err error =>
      cases error with
      | abort error => rfl
      | raise value =>
        cases value with
        | exn value => rfl
        | ret values => exact False.elim (notReturn ⟨values, rfl⟩)
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, firstOutcome⟩ :=
    ihArgs (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at firstOutcome
  | none =>
    have jumpMid : DataSem.jumpExc t1 ≠ none → DataSem.jumpExc tmid ≠ none := firstOutcome.2.2.2.2.2.2.2.2.2.1
    have resultVars : DataProps.varCorr values argNames (sptMap dataToBviValue tmid.locals) := firstOutcome.2.2.2.2.2.2.2.2.2.2
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedCode : BvlSem.findCode dest (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
      simpa [← projected] using sourceCode
    obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
      findCode_projection dest dataValues smid tmid callArgs body middleRel projectedCode
    subst callArgs
    have targetClock : ticks + 1 ≤ tmid.clock := by simpa [← middleRel.1] using clock
    let afterTicks := { tmid with clock := tmid.clock - ticks }
    have positive : afterTicks.clock ≠ 0 := by simp only [afterTicks]; omega
    have afterRead : DataSem.getVars argNames afterTicks.locals = some dataValues := by simpa [afterTicks] using read
    have afterCode : DataSem.findCode dest dataValues afterTicks.code afterTicks.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by simpa [afterTicks] using targetCode
    have entryRel : stateRel (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) := by
      have entry := stateRel_callEntry smid tmid dataArgs size ticks middleRel
      simpa [stateRel, DataSem.callEnv, afterTicks] using entry
    have callJump : isException res → DataSem.jumpExc (DataSem.callEnv dataArgs size (DataSem.decClock afterTicks)) ≠ none := by
      intro exception
      have available := jumpMid (exceptionJump exception)
      cases old : DataSem.jumpExc tmid with
      | none => exact False.elim (available old)
      | some jumped =>
        have moved := DataSem.jumpExc_transport tmid (DataSem.callEnv dataArgs size (DataSem.decClock afterTicks))
          jumped rfl rfl old
        rw [moved]
        simp
    obtain ⟨result, final, bodyNames, next, lsBody, localsSize, stackMax, safe, peak, bodyTarget,
        finalRel, optimizedRel, bodyOutcome⟩ :=
      compileExp_callEnv body dataArgs (BviSem.decClock (ticks + 1) smid) s2 res (DataSem.decClock afterTicks) size
        ihBody bodyRun notType entryRel callJump
    let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
    have optOutcome := correctOutcome_some_resources res (DataSem.callEnv dataArgs size (DataSem.decClock afterTicks))
      final dataArgs.length next (List.range dataArgs.length) [] bodyNames (dataArgs.map dataToBviValue) true
      result lsBody localsSize stackMax safe peak bodyOutcome
    let call := DataLang.Prog.call none dest argNames none
    have callRun : DataSem.evaluate call afterTicks = (some result, optimized) := by
      simp [call, DataSem.evaluate, afterRead, afterCode, positive, bodyTarget, optimized]
    have ticksRun : DataSem.evaluate (DataLang.mkTicks ticks call) tmid = (some result, optimized) := by
      rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
      exact callRun
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRun := evaluateSeq_continue argsProg (DataLang.mkTicks ticks call) t1 tmid _ target targetBound ticksRun
    have secondOutcome : correctOutcome res tmid optimized n1 (n1 + 1) corr live [n1] env true (some result) lsBody := by
      simpa [correctOutcome, DataSem.callEnv, DataSem.decClock, afterTicks, optimized] using optOutcome
    refine ⟨wholeRun, optimized, .seq argsProg (DataLang.mkTicks ticks call), some result, [n1], n1 + 1,
      lsBody, ?_, targetRun, optimizedRel, ?_⟩
    · simp [compileSource, compiled, call]
    · exact correctOutcome_seq values res t1 tmid optimized n n1 (n1 + 1) corr live argNames [n1] env true
        (some result) ls lsBody firstOutcome secondOutcome

/-- An error while evaluating unhandled-call arguments propagates before
the call executes. This is untagged pending evaluator correspondence review. -/
theorem simulationFor_call_argsError {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    let rest := DataLang.mkTicks ticks (.call (if tail then none else some ([n1], namesOfList (live ++ corr))) dest argNames none)
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using sourceBound
    have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some result, t2) :=
      evaluateSeq_stop argsProg rest t1 t2 result target targetBound
    refine ⟨wholeRun, t2, .seq argsProg rest, some result, [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
    · simp [compileSource, compiled, rest]
    · simpa [correctOutcome, isResult] using outcome

/-- An error while evaluating the arguments of a direct call with a handler
propagates before the handler or call executes. -/
theorem simulationFor_call_handler_argsError {C F : Type} (ticks dest : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F)
    (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks (some dest) args (some handler)] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    generalize handlerCompiled : compileSource (n1 + 1) (n1 :: corr) false live [handler] = triple
    obtain ⟨handlerProg, handlerNames, n2⟩ := triple
    let after := if tail then DataLang.Prog.return [n2] else .skip
    let rest := DataLang.mkTicks ticks (.seq
      (.call (some ([n2], namesOfList (live ++ corr))) (some dest) argNames
        (some (n1, .seq handlerProg (.move n2 (Flapjack.holHd handlerNames))))) after)
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using sourceBound
    have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some result, t2) :=
      evaluateSeq_stop argsProg rest t1 t2 result target targetBound
    refine ⟨wholeRun, t2, .seq argsProg rest, some result, [n2], n2 + 1, ls, ?_, targetRun, finalRel, ?_⟩
    · simp [compileSource, compiled, handlerCompiled, rest, after]
    · simpa [correctOutcome, isResult] using outcome

/-- Errors in let-call arguments propagate before either the call or its
continuation executes, including the tail-call rewrite. -/
theorem simulationFor_letCall_argsError {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F)
    (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.letCall rets ticks dest args body] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.letCall rets ticks dest args body] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  classical
  have wholeRun : BviSem.evaluate [.letCall rets ticks dest args body] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using sourceBound
    by_cases identity : body = .return ((List.range rets).map Bvi.Exp.var)
    · let rest := DataLang.mkTicks ticks (.call none (some dest) argNames none)
      have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some result, t2) :=
        evaluateSeq_stop argsProg rest t1 t2 result target targetBound
      refine ⟨wholeRun, t2, .seq argsProg rest, some result, [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, rest]
      · simpa [correctOutcome, isResult] using outcome
    · let returns := (List.range rets).map (n1 + ·)
      generalize bodyCompiled : compileSource (n1 + rets) (returns ++ corr) tail live [body] = triple
      obtain ⟨bodyProg, bodyNames, n2⟩ := triple
      let rest := DataLang.mkTicks ticks (.call (some (returns, namesOfList (live ++ corr))) (some dest) argNames none)
      let inner := DataLang.Prog.seq argsProg rest
      have innerRun : DataSem.evaluate inner t1 = (some result, t2) :=
        evaluateSeq_stop argsProg rest t1 t2 result target targetBound
      have targetRun : DataSem.evaluate (.seq inner bodyProg) t1 = (some result, t2) :=
        evaluateSeq_stop inner bodyProg t1 t2 result innerRun targetBound
      refine ⟨wholeRun, t2, .seq inner bodyProg, some result, bodyNames, n2, ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, bodyCompiled, inner, rest, returns]
      · simpa [correctOutcome, isResult] using outcome

end Flapjack.Compiler.Backend.BviToData
