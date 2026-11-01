import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.BviToData.Proofs.Optimise
import Flapjack.Compiler.Backend.BviToData.Proofs.FindCode
import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
import Flapjack.Compiler.Backend.Semantics.DataProps.Ticks
import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush
import Flapjack.Misc.Sptree.UnionAlgebra
import Mathlib.Data.List.Induction

/-! Call argument cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem setVars_singleton {C F : Type} (name : Nat) (value : DataSem.Value) (state : DataSem.State C F) :
    DataSem.setVars [name] [value] state = DataSem.setVar name value state := by
  simp [DataSem.setVars, DataSem.setVar, sptFromAList, sptUnion_insert_ln]

/-- An exception jump through a saved ordinary frame selects the same caller handler. -/
theorem jumpExc_remove_saved_frame {C F : Type} (target final : DataSem.State C F)
    (cut : Spt DataSem.Value) (ls : Option Nat)
    (jump : DataSem.jumpExc { final with stack := .env target.localsSize cut :: target.stack, handler := target.handler } =
      some { final with localsSize := ls }) :
    DataSem.jumpExc { final with stack := target.stack, handler := target.handler } =
      some { final with localsSize := ls } := by
  let base := { final with stack := target.stack, handler := target.handler, localsSize := target.localsSize }
  have transported := DataSem.jumpExc_transport
    { final with stack := .env target.localsSize cut :: target.stack, handler := target.handler }
    (DataSem.pushEnv cut false base) { final with localsSize := ls }
    (by simp [DataSem.pushEnv, base]) (by simp [DataSem.pushEnv, base]) jump
  rw [DataSem.jumpExc_pushEnv_noHandler] at transported
  cases baseJump : DataSem.jumpExc base with
  | none => simp [baseJump] at transported
  | some jumped =>
    simp only [baseJump, Option.map_some, Option.some.injEq] at transported
    have finalJump := DataSem.jumpExc_transport base
      { final with stack := target.stack, handler := target.handler } jumped rfl rfl baseJump
    rw [finalJump]
    congr 1
    have stackEq := congrArg DataSem.State.stack transported
    have handlerEq := congrArg DataSem.State.handler transported
    have localsEq := congrArg DataSem.State.locals transported
    have sizeEq := congrArg DataSem.State.localsSize transported
    cases final
    simp_all

/-- A jump to the handler frame installed for a call restores the caller's
control and saved locals. -/
theorem jumpExc_handler_frame {C F : Type} (target final : DataSem.State C F)
    (cut : Spt DataSem.Value) (ls : Option Nat)
    (jump : DataSem.jumpExc { final with stack := .exc target.localsSize cut target.handler :: target.stack, handler := target.stack.length } =
      some { final with localsSize := ls }) :
    final.stack = target.stack ∧ final.handler = target.handler ∧ final.locals = cut ∧ ls = target.localsSize := by
  have equal : { final with stack := target.stack, handler := target.handler, locals := cut, localsSize := target.localsSize } =
      { final with localsSize := ls } := by
    simpa [DataSem.jumpExc] using jump
  have stack := congrArg DataSem.State.stack equal
  have handler := congrArg DataSem.State.handler equal
  have locals := congrArg DataSem.State.locals equal
  have size := congrArg DataSem.State.localsSize equal
  exact ⟨stack.symm, handler.symm, locals.symm, size.symm⟩

/-- Binding a caught exception in the fresh handler local preserves the
caller's live locals, variable correspondence, and control stack. -/
theorem correctOutcome_catch_entry {C F : Type} (target caught : DataSem.State C F)
    (n : Nat) (corr live : List Nat) (env : List BvlSem.Value)
    (value : BvlSem.Value) (dataValue : DataSem.Value)
    (projected : dataToBviValue dataValue = value)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (locals : caught.locals = sptMkWf (sptInter target.locals (namesOfList (live ++ corr))))
    (stack : caught.stack = target.stack) (handler : caught.handler = target.handler) :
    correctOutcome (.val [value]) target (DataSem.setVar n dataValue caught) n (n + 1)
      corr live [n] env false none none := by
  let roots := live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  let next := DataSem.setVar n dataValue caught
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
    simpa [roots, DataSem.getVars] using
      (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
  have nextLocals : next.locals = sptInsert n dataValue cut := by
    simp [next, DataSem.setVar, locals, cut, roots]
  have destRead : sptLookup n next.locals = some dataValue := by simp [nextLocals, sptLookup_sptInsert_same]
  have lookupOther : ∀ key, key ≠ n → sptLookup key next.locals =
      if key ∈ roots then sptLookup key target.locals else none := by
    intro key different
    rw [nextLocals, sptLookup_sptInsert_ne n key dataValue cut different]
    exact lookup_cut_namesOfList roots target.locals key
  have keeps : ∀ key ∈ roots, key ≠ n → sptLookup key next.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different, if_pos member]
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue next.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals next.locals corr env vars
    intro key member
    have root : key ∈ roots := by simp [roots, member]
    have different : key ≠ n := by
      intro equal
      subst key
      exact rootsPresent n root (fresh n (Nat.le_refl n))
    exact keeps key root different
  change correctOutcome (.val [value]) target next n (n + 1) corr live [n] env false none none
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
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
  · simp [next, DataSem.setVar, stack]
  · simp [next, DataSem.setVar, handler]
  · intro available
    cases old : DataSem.jumpExc target with
    | none => exact False.elim (available old)
    | some jumped =>
      have moved := DataSem.jumpExc_transport target next jumped
        (by simp [next, DataSem.setVar, stack]) (by simp [next, DataSem.setVar, handler]) old
      rw [moved]
      simp
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- Once an exception has restored the caller frame, the recursively simulated
handler can run with the caught value in its fresh local and move its result
to the handler's merge local. -/
theorem simulationFor_caught_handler {C F : Type} (handler : Bvi.Exp)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (value : BvlSem.Value) (dataValue : DataSem.Value) (res : BviSem.BviResult)
    (target caught : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (ih : simulationFor [handler] (value :: env) source)
    (run : BviSem.evaluate [handler] (value :: env) source = (res, nextSource))
    (notType : res ≠ .err (.abort .typeError))
    (projected : dataToBviValue dataValue = value)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (locals : caught.locals = sptMkWf (sptInter target.locals (namesOfList (live ++ corr))))
    (stack : caught.stack = target.stack) (handlerEq : caught.handler = target.handler)
    (related : stateRel source caught)
    (exceptionJump : isException res → DataSem.jumpExc target ≠ none) :
    ∃ hprog hname next targetNext pres ls,
      compileSource (n + 1) (n :: corr) false live [handler] = (hprog, [hname], next) ∧
      DataSem.evaluate (.seq hprog (.move next hname)) (DataSem.setVar n dataValue caught) = (pres, targetNext) ∧
      stateRel nextSource targetNext ∧
      correctOutcome res target targetNext n (next + 1) corr live [next] env false pres ls := by
  let start := DataSem.setVar n dataValue caught
  have base : correctOutcome (.val [value]) target start n (n + 1) corr live [n] env false none none :=
    correctOutcome_catch_entry target caught n corr live env value dataValue projected vars fresh livePresent locals stack handlerEq
  have startRel : stateRel source start := by simpa [start, DataSem.setVar, stateRel] using related
  have liveAll := correctOutcome_live [value] target start n (n + 1) corr live [n] env none base livePresent
  have liveStart : ∀ key ∈ live, sptLookup key start.locals ≠ none := by
    intro key member
    exact liveAll key (List.mem_append_right [n] member)
  have freshStart : ∀ key, n + 1 ≤ key → sptLookup key start.locals = none := base.2.2.2.1
  have oldVars : DataProps.varCorr env corr (sptMap dataToBviValue start.locals) := base.2.2.2.2.1
  have valueVars : DataProps.varCorr [value] [n] (sptMap dataToBviValue start.locals) := base.2.2.2.2.2.2.2.2.2.2
  have handlerVars : DataProps.varCorr (value :: env) (n :: corr) (sptMap dataToBviValue start.locals) := by
    cases valueVars with
    | cons read _ => exact .cons read oldVars
  have jumpStart : isException res → DataSem.jumpExc start ≠ none := by
    intro exception
    exact base.2.2.2.2.2.2.2.2.2.1 (exceptionJump exception)
  obtain ⟨final, hprog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩ :=
    ih res nextSource start (n + 1) (n :: corr) false live run notType handlerVars (by simp) freshStart startRel liveStart jumpStart
  have length := compileSource_LENGTH (n + 1) (n :: corr) false live [handler] hprog names next compiled
  cases names with
  | nil => simp at length
  | cons name rest =>
    cases rest with
    | cons second more => simp at length
    | nil =>
      obtain ⟨targetNext, presFinal, movedRun, movedRel, movedOutcome⟩ :=
        simulation_branch_move handler (value :: env) source nextSource start final res (n + 1) next next name
          (n :: corr) live hprog pres ls run targetRun startRel finalRel outcome (Nat.le_refl next)
      refine ⟨hprog, name, next, targetNext, presFinal, ls, compiled, movedRun, movedRel, ?_⟩
      exact correctOutcome_let [value] res target start targetNext n (n + 1) (next + 1) corr live [n] [next]
        env false presFinal none ls base (by simpa using movedOutcome)

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

/-- A returning call with sufficient clock propagates an abort from its
recursive callee, without entering the caller continuation. -/
theorem simulationFor_call_nontail_abort {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid s2 : BviSem.BviState C F) (error : Abort)
    (ihArgs : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (clock : ticks + 1 ≤ smid.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (.err (.abort error), s2))
    (notType : error ≠ .typeError)
    (ihBody : simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid))
    (t1 : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.abort error), s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr false live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err (.abort error)) t1 t2 n next corr live names env false pres ls := by
  have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
      (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (.err (.abort error), s2) := by
    rw [BviSem.fixClock_evaluate, bodyRun]
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.abort error), s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show ¬ smid.clock < ticks + 1 by omega, bodyClamped]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, firstOutcome⟩ :=
    ihArgs (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at firstOutcome
  | none =>
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls firstOutcome livePresent
    have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
      intro key member
      exact liveMidAll key (List.mem_append_right argNames member)
    have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := firstOutcome.2.2.2.2.1
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
    let roots := live ++ corr
    let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
    have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
      simpa [roots, DataSem.getVars] using
        (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
    have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
      cutEnv_namesOfList roots tmid.locals rootsPresent
    let pushed := DataSem.pushEnv cut false (DataSem.decClock afterTicks)
    have entryRel : stateRel (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) := by
      have entry := stateRel_callEntry smid tmid dataArgs size ticks middleRel
      simpa [stateRel, DataSem.callEnv, afterTicks] using entry
    have pushedRel := stateRel_pushEnv (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) cut false entryRel
    obtain ⟨result, final, bodyNames, next, lsBody, localsSize, stackMax, safe, peak, bodyTarget,
        finalRel, optimizedRel, bodyOutcome⟩ :=
      compileExp_callEnv body dataArgs (BviSem.decClock (ticks + 1) smid) s2 (.err (.abort error)) pushed size
        ihBody bodyRun (by simpa using notType) pushedRel (by simp [isException])
    have resultEq : result = .err (.abort error) := by
      have projection := bodyOutcome.1 (by simp [isReturn])
      cases result with
      | val values => simp [dataToBviResult] at projection
      | err failure => cases failure with
        | abort reason => simpa [dataToBviResult] using projection
        | raise value => simp [dataToBviResult] at projection
    subst result
    let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
    have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
        (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
        (some (.err (.abort error)), optimized) := by
      rw [DataSem.fixClock_evaluate, bodyTarget]
    let call := DataLang.Prog.call (some ([n1], namesOfList roots)) dest argNames none
    have callRun : DataSem.evaluate call afterTicks = (some (.err (.abort error)), optimized) := by
      simp only [call, DataSem.evaluate, afterRead, afterCode, List.nodup_singleton, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, cutEnv, positive, Option.isSome_none]
      rw [clamped]
    have ticksRun : DataSem.evaluate (DataLang.mkTicks ticks call) tmid = (some (.err (.abort error)), optimized) := by
      rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
      exact callRun
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRun := evaluateSeq_continue argsProg (DataLang.mkTicks ticks call) t1 tmid _ target targetBound ticksRun
    refine ⟨wholeRun, optimized, .seq argsProg (DataLang.mkTicks ticks call), some (.err (.abort error)),
      [n1], n1 + 1, lsBody, ?_, targetRun, optimizedRel, ?_⟩
    · simp [compileSource, compiled, call, roots]
    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- A returning call propagates an unhandled exception from its recursive
callee across the saved caller frame. -/
theorem simulationFor_call_nontail_exception {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid s2 : BviSem.BviState C F) (value : BvlSem.Value)
    (ihArgs : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (clock : ticks + 1 ≤ smid.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (.err (.raise (.exn value)), s2))
    (ihBody : simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid))
    (t1 : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.raise (.exn value)), s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr false live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err (.raise (.exn value))) t1 t2 n next corr live names env false pres ls := by
  have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
      (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (.err (.raise (.exn value)), s2) := by
    rw [BviSem.fixClock_evaluate, bodyRun]
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 = (.err (.raise (.exn value)), s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show ¬ smid.clock < ticks + 1 by omega, bodyClamped]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, firstOutcome⟩ :=
    ihArgs (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at firstOutcome
  | none =>
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls firstOutcome livePresent
    have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
      intro key member
      exact liveMidAll key (List.mem_append_right argNames member)
    have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := firstOutcome.2.2.2.2.1
    have jumpMid : DataSem.jumpExc tmid ≠ none := firstOutcome.2.2.2.2.2.2.2.2.2.1 exceptionJump
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
    let roots := live ++ corr
    let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
    have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
      simpa [roots, DataSem.getVars] using
        (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
    have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
      cutEnv_namesOfList roots tmid.locals rootsPresent
    let pushed := DataSem.pushEnv cut false (DataSem.decClock afterTicks)
    have entryRel : stateRel (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) := by
      have entry := stateRel_callEntry smid tmid dataArgs size ticks middleRel
      simpa [stateRel, DataSem.callEnv, afterTicks] using entry
    have pushedRel := stateRel_pushEnv (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) cut false entryRel
    have callJump : DataSem.jumpExc (DataSem.callEnv dataArgs size pushed) ≠ none := by
      change DataSem.jumpExc (DataSem.callEnv dataArgs size (DataSem.pushEnv cut false (DataSem.decClock afterTicks))) ≠ none
      rw [DataSem.jumpExc_callEnv_push_noHandler]
      cases h : DataSem.jumpExc afterTicks with
      | none =>
        cases original : DataSem.jumpExc tmid with
        | none => exact False.elim (jumpMid original)
        | some jumped =>
          have moved := DataSem.jumpExc_transport tmid afterTicks jumped rfl rfl original
          rw [h] at moved
          contradiction
      | some jumped => simp
    obtain ⟨result, final, bodyNames, next, lsBody, localsSize, stackMax, safe, peak, bodyTarget,
        finalRel, optimizedRel, bodyOutcome⟩ :=
      compileExp_callEnv body dataArgs (BviSem.decClock (ticks + 1) smid) s2 (.err (.raise (.exn value))) pushed size
        ihBody bodyRun (by simp) pushedRel (by intro _; exact callJump)
    have projection := bodyOutcome.1 (by simp [isReturn])
    rw [dataToBviResult_eq] at projection
    obtain ⟨dataValue, resultEq, projectedValue⟩ := projection
    simp only [BviSem.ExnOrRet.exn.injEq] at projectedValue
    subst result
    let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
    have optOutcome := correctOutcome_some_resources (.err (.raise (.exn value))) (DataSem.callEnv dataArgs size pushed)
      final dataArgs.length next (List.range dataArgs.length) [] bodyNames (dataArgs.map dataToBviValue) true
      (.err (.raise dataValue)) lsBody localsSize stackMax safe peak bodyOutcome
    have innerJump := optOutcome.2.2.2.2 (by simp [isException])
    have savedJump : DataSem.jumpExc { optimized with stack := .env tmid.localsSize cut :: tmid.stack, handler := tmid.handler } =
        some { optimized with localsSize := lsBody } := by
      simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock, afterTicks, optimized] using innerJump
    have finalJump := jumpExc_remove_saved_frame tmid optimized cut lsBody savedJump
    have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
        (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
        (some (.err (.raise dataValue)), optimized) := by
      rw [DataSem.fixClock_evaluate, bodyTarget]
    let call := DataLang.Prog.call (some ([n1], namesOfList roots)) dest argNames none
    have callRun : DataSem.evaluate call afterTicks = (some (.err (.raise dataValue)), optimized) := by
      simp only [call, DataSem.evaluate, afterRead, afterCode, List.nodup_singleton, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, cutEnv, positive, Option.isSome_none]
      rw [clamped]
    have ticksRun : DataSem.evaluate (DataLang.mkTicks ticks call) tmid = (some (.err (.raise dataValue)), optimized) := by
      rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
      exact callRun
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRun := evaluateSeq_continue argsProg (DataLang.mkTicks ticks call) t1 tmid _ target targetBound ticksRun
    have secondOutcome : correctOutcome (.err (.raise (.exn value))) tmid optimized n1 (n1 + 1)
        corr live [n1] env false (some (.err (.raise dataValue))) lsBody := by
      simp [correctOutcome, dataToBviResult, isReturn, isResult, isException, projectedValue, finalJump]
    refine ⟨wholeRun, optimized, .seq argsProg (DataLang.mkTicks ticks call), some (.err (.raise dataValue)),
      [n1], n1 + 1, lsBody, ?_, targetRun, optimizedRel, ?_⟩
    · simp [compileSource, compiled, call, roots]
    · exact correctOutcome_seq values (.err (.raise (.exn value))) t1 tmid optimized n n1 (n1 + 1)
        corr live argNames [n1] env false (some (.err (.raise dataValue))) ls lsBody firstOutcome secondOutcome

/-- A returning call restores its saved caller frame and binds the value
returned by its recursively simulated callee. -/
theorem simulationFor_call_nontail_value {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid s2 : BviSem.BviState C F) (value : BvlSem.Value)
    (ihArgs : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode dest values smid.code = some (callArgs, body))
    (clock : ticks + 1 ≤ smid.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (.val [value], s2))
    (ihBody : simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid))
    (t1 : DataSem.State C F) (n : Nat) (corr live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.val [value], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr false live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [value]) t1 t2 n next corr live names env false pres ls := by
  have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
      (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (.val [value], s2) := by
    rw [BviSem.fixClock_evaluate, bodyRun]
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 = (.val [value], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show ¬ smid.clock < ticks + 1 by omega, bodyClamped]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, firstOutcome⟩ :=
    ihArgs (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at firstOutcome
  | none =>
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls firstOutcome livePresent
    have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
      intro key member
      exact liveMidAll key (List.mem_append_right argNames member)
    have freshMid : ∀ key, n1 ≤ key → sptLookup key tmid.locals = none := firstOutcome.2.2.2.1
    have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := firstOutcome.2.2.2.2.1
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
    let roots := live ++ corr
    let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
    have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
      simpa [roots, DataSem.getVars] using
        (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
    have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
      cutEnv_namesOfList roots tmid.locals rootsPresent
    let pushed := DataSem.pushEnv cut false (DataSem.decClock afterTicks)
    have entryRel : stateRel (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) := by
      have entry := stateRel_callEntry smid tmid dataArgs size ticks middleRel
      simpa [stateRel, DataSem.callEnv, afterTicks] using entry
    have pushedRel := stateRel_pushEnv (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) cut false entryRel
    obtain ⟨result, final, bodyNames, next, lsBody, localsSize, stackMax, safe, peak, bodyTarget,
        finalRel, optimizedRel, bodyOutcome⟩ :=
      compileExp_callEnv body dataArgs (BviSem.decClock (ticks + 1) smid) s2 (.val [value]) pushed size
        ihBody bodyRun (by simp) pushedRel (by simp [isException])
    obtain ⟨dataValue, resultEq, valueProjection⟩ : ∃ dataValue, result = .val [dataValue] ∧ dataToBviValue dataValue = value := by
      have projection := bodyOutcome.1 (by simp [isReturn])
      cases result with
      | err error => cases error <;> simp [dataToBviResult] at projection
      | val results =>
        cases results with
        | nil => simp [dataToBviResult] at projection
        | cons head rest =>
          cases rest with
          | nil => exact ⟨head, rfl, by simpa [dataToBviResult] using projection⟩
          | cons second rest => simp [dataToBviResult] at projection
    subst result
    have control := bodyOutcome.2.2.1 (by simp [isResult])
    have stack : final.stack = .env tmid.localsSize cut :: tmid.stack := by
      simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock, afterTicks] using control.1.symm
    have handler : final.handler = tmid.handler := by
      simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock, afterTicks] using control.2.symm
    let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
    let restored := { optimized with stack := tmid.stack, locals := cut, localsSize := tmid.localsSize }
    let targetNext := DataSem.setVar n1 dataValue restored
    have pop : DataSem.popEnv optimized = some restored := by simp [DataSem.popEnv, optimized, stack, restored]
    have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
        (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
        (some (.val [dataValue]), optimized) := by
      rw [DataSem.fixClock_evaluate, bodyTarget]
    let call := DataLang.Prog.call (some ([n1], namesOfList roots)) dest argNames none
    have callRun : DataSem.evaluate call afterTicks = (none, targetNext) := by
      simp only [call, DataSem.evaluate, afterRead, afterCode, List.nodup_singleton, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, cutEnv, positive, Option.isSome_none]
      rw [clamped, pop]
      simp [setVars_singleton, targetNext]
    have ticksRun : DataSem.evaluate (DataLang.mkTicks ticks call) tmid = (none, targetNext) := by
      rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
      exact callRun
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRun := evaluateSeq_continue argsProg (DataLang.mkTicks ticks call) t1 tmid _ target targetBound ticksRun
    have targetRel : stateRel s2 targetNext := by
      simpa [targetNext, restored, DataSem.setVar, stateRel, optimized] using optimizedRel
    have locals : targetNext.locals = sptInsert n1 dataValue cut := by simp [targetNext, restored, DataSem.setVar]
    have destRead : sptLookup n1 targetNext.locals = some dataValue := by simp [locals, sptLookup_sptInsert_same]
    have lookupOther : ∀ key, key ≠ n1 → sptLookup key targetNext.locals =
        if key ∈ roots then sptLookup key tmid.locals else none := by
      intro key different
      rw [locals, sptLookup_sptInsert_ne n1 key dataValue cut different]
      exact lookup_cut_namesOfList roots tmid.locals key
    have keeps : ∀ key ∈ roots, key ≠ n1 → sptLookup key targetNext.locals = sptLookup key tmid.locals := by
      intro key member different
      rw [lookupOther key different, if_pos member]
    have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
      apply varCorr_of_lookup_eq dataToBviValue tmid.locals targetNext.locals corr env varsMid
      intro key member
      have root : key ∈ roots := by simp [roots, member]
      have different : key ≠ n1 := by
        intro equal
        subst key
        exact rootsPresent n1 root (freshMid n1 (Nat.le_refl n1))
      exact keeps key root different
    have secondOutcome : correctOutcome (.val [value]) tmid targetNext n1 (n1 + 1) corr live [n1] env false none none := by
      simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
      refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro key bound
        have different : key ≠ n1 := by omega
        rw [lookupOther key different]
        simp [freshMid key (by omega)]
      · intro key v lookup
        by_cases equal : key = n1
        · omega
        · have oldLookup : sptLookup key tmid.locals = some v := by
            rw [lookupOther key equal] at lookup
            split at lookup <;> simp_all
          by_contra bound
          have absent := freshMid key (by omega)
          rw [oldLookup] at absent
          contradiction
      · intro key v lookup needed
        have different : key ≠ n1 := by
          intro equal
          subst key
          have absent := freshMid n1 (Nat.le_refl n1)
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
        cases old : DataSem.jumpExc tmid with
        | none => exact False.elim (available old)
        | some jumped =>
          have moved := DataSem.jumpExc_transport tmid targetNext jumped
            (by simp [targetNext, restored, DataSem.setVar])
            (by simp [targetNext, restored, DataSem.setVar, optimized, handler]) old
          rw [moved]
          simp
      · constructor
        · simp [DataSem.getVar, sptLookup_sptMap, destRead, valueProjection]
        · constructor
    refine ⟨wholeRun, targetNext, .seq argsProg (DataLang.mkTicks ticks call), none,
      [n1], n1 + 1, none, ?_, targetRun, targetRel, ?_⟩
    · simp [compileSource, compiled, call, roots]
    · exact correctOutcome_seq values (.val [value]) t1 tmid targetNext n n1 (n1 + 1)
        corr live argNames [n1] env false none ls none firstOutcome secondOutcome

/-- A handled call restores the saved handler frame and binds the
value returned by its recursively simulated callee. -/
theorem simulationFor_call_handler_value {C F : Type} (ticks dest : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid s2 : BviSem.BviState C F) (value : BvlSem.Value)
    (ihArgs : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, body))
    (clock : ticks + 1 ≤ smid.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (.val [value], s2))
    (ihBody : simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.val [value], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks (some dest) args (some handler)] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [value]) t1 t2 n next corr live names env tail pres ls := by
  have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
      (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (.val [value], s2) := by
    rw [BviSem.fixClock_evaluate, bodyRun]
  have wholeRun : BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.val [value], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show ¬ smid.clock < ticks + 1 by omega, bodyClamped]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, firstOutcome⟩ :=
    ihArgs (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at firstOutcome
  | none =>
    generalize handlerCompiled : compileSource (n1 + 1) (n1 :: corr) false live [handler] = triple
    obtain ⟨handlerProg, handlerNames, n2⟩ := triple
    have destBound : n1 + 1 ≤ n2 := compileSource_LESS_EQ (n1 + 1) (n1 :: corr) false live [handler] handlerProg handlerNames n2 handlerCompiled
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls firstOutcome livePresent
    have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
      intro key member
      exact liveMidAll key (List.mem_append_right argNames member)
    have freshMid : ∀ key, n1 ≤ key → sptLookup key tmid.locals = none := firstOutcome.2.2.2.1
    have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := firstOutcome.2.2.2.2.1
    have resultVars : DataProps.varCorr values argNames (sptMap dataToBviValue tmid.locals) := firstOutcome.2.2.2.2.2.2.2.2.2.2
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedCode : BvlSem.findCode (some dest) (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
      simpa [← projected] using sourceCode
    obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
      findCode_projection (some dest) dataValues smid tmid callArgs body middleRel projectedCode
    subst callArgs
    have targetClock : ticks + 1 ≤ tmid.clock := by simpa [← middleRel.1] using clock
    let afterTicks := { tmid with clock := tmid.clock - ticks }
    have positive : afterTicks.clock ≠ 0 := by simp only [afterTicks]; omega
    have afterRead : DataSem.getVars argNames afterTicks.locals = some dataValues := by simpa [afterTicks] using read
    have afterCode : DataSem.findCode (some dest) dataValues afterTicks.code afterTicks.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by simpa [afterTicks] using targetCode
    let roots := live ++ corr
    let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
    have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
      simpa [roots, DataSem.getVars] using
        (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
    have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
      cutEnv_namesOfList roots tmid.locals rootsPresent
    let pushed := DataSem.pushEnv cut true (DataSem.decClock afterTicks)
    have entryRel : stateRel (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) := by
      have entry := stateRel_callEntry smid tmid dataArgs size ticks middleRel
      simpa [stateRel, DataSem.callEnv, afterTicks] using entry
    have pushedRel := stateRel_pushEnv (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) cut true entryRel
    obtain ⟨result, final, bodyNames, next, lsBody, localsSize, stackMax, safe, peak, bodyTarget,
        finalRel, optimizedRel, bodyOutcome⟩ :=
      compileExp_callEnv body dataArgs (BviSem.decClock (ticks + 1) smid) s2 (.val [value]) pushed size
        ihBody bodyRun (by simp) pushedRel (by simp [isException])
    obtain ⟨dataValue, resultEq, valueProjection⟩ : ∃ dataValue, result = .val [dataValue] ∧ dataToBviValue dataValue = value := by
      have projection := bodyOutcome.1 (by simp [isReturn])
      cases result with
      | err error => cases error <;> simp [dataToBviResult] at projection
      | val results =>
        cases results with
        | nil => simp [dataToBviResult] at projection
        | cons head rest =>
          cases rest with
          | nil => exact ⟨head, rfl, by simpa [dataToBviResult] using projection⟩
          | cons second rest => simp [dataToBviResult] at projection
    subst result
    have control := bodyOutcome.2.2.1 (by simp [isResult])
    have stack : final.stack = .exc tmid.localsSize cut tmid.handler :: tmid.stack := by
      simpa [DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock, afterTicks] using control.1.symm
    let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
    let restored := { optimized with stack := tmid.stack, locals := cut, localsSize := tmid.localsSize, handler := tmid.handler }
    let targetNext := DataSem.setVar n2 dataValue restored
    have pop : DataSem.popEnv optimized = some restored := by simp [DataSem.popEnv, optimized, stack, restored]
    have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
        (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
        (some (.val [dataValue]), optimized) := by
      rw [DataSem.fixClock_evaluate, bodyTarget]
    let call := DataLang.Prog.call (some ([n2], namesOfList roots)) (some dest) argNames
      (some (n1, .seq handlerProg (.move n2 (Flapjack.holHd handlerNames))))
    have callRun : DataSem.evaluate call afterTicks = (none, targetNext) := by
      simp only [call, DataSem.evaluate, afterRead, afterCode, List.nodup_singleton, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, cutEnv, positive, Option.isSome_some]
      rw [clamped, pop]
      simp [setVars_singleton, targetNext]
    have callBound := DataSem.evaluate_clock_le call afterTicks
    rw [callRun] at callBound
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRel : stateRel s2 targetNext := by
      simpa [targetNext, restored, DataSem.setVar, stateRel, optimized] using optimizedRel
    have locals : targetNext.locals = sptInsert n2 dataValue cut := by simp [targetNext, restored, DataSem.setVar]
    have destRead : sptLookup n2 targetNext.locals = some dataValue := by simp [locals, sptLookup_sptInsert_same]
    have lookupOther : ∀ key, key ≠ n2 → sptLookup key targetNext.locals =
        if key ∈ roots then sptLookup key tmid.locals else none := by
      intro key different
      rw [locals, sptLookup_sptInsert_ne n2 key dataValue cut different]
      exact lookup_cut_namesOfList roots tmid.locals key
    have keeps : ∀ key ∈ roots, key ≠ n2 → sptLookup key targetNext.locals = sptLookup key tmid.locals := by
      intro key member different
      rw [lookupOther key different, if_pos member]
    have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
      apply varCorr_of_lookup_eq dataToBviValue tmid.locals targetNext.locals corr env varsMid
      intro key member
      have root : key ∈ roots := by simp [roots, member]
      have different : key ≠ n2 := by
        intro equal
        subst key
        exact rootsPresent n2 root (freshMid n2 (by omega))
      exact keeps key root different
    have secondOutcome : correctOutcome (.val [value]) tmid targetNext n1 (n2 + 1) corr live [n2] env false none none := by
      simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
      refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro key bound
        have different : key ≠ n2 := by omega
        rw [lookupOther key different]
        simp [freshMid key (by omega)]
      · intro key v lookup
        by_cases equal : key = n2
        · omega
        · have oldLookup : sptLookup key tmid.locals = some v := by
            rw [lookupOther key equal] at lookup
            split at lookup <;> simp_all
          by_contra bound
          have absent := freshMid key (by omega)
          rw [oldLookup] at absent
          contradiction
      · intro key v lookup needed
        have different : key ≠ n2 := by
          intro equal
          subst key
          have absent := freshMid n2 (by omega)
          rw [lookup] at absent
          contradiction
        have root : key ∈ roots := by
          by_cases member : key ∈ live
          · simp [roots, member]
          · simp [roots, needed member]
        rw [keeps key root different]
        exact lookup
      · simp [targetNext, restored, DataSem.setVar]
      · simp [targetNext, restored, DataSem.setVar, optimized]
      · intro available
        cases old : DataSem.jumpExc tmid with
        | none => exact False.elim (available old)
        | some jumped =>
          have moved := DataSem.jumpExc_transport tmid targetNext jumped
            (by simp [targetNext, restored, DataSem.setVar])
            (by simp [targetNext, restored, DataSem.setVar, optimized]) old
          rw [moved]
          simp
      · constructor
        · simp [DataSem.getVar, sptLookup_sptMap, destRead, valueProjection]
        · constructor
    cases tail with
    | false =>
      have seqRun : DataSem.evaluate (.seq call .skip) afterTicks = (none, targetNext) :=
        evaluateSeq_continue call .skip afterTicks targetNext _ callRun callBound (by simp [DataSem.evaluate])
      let rest := DataLang.mkTicks ticks (.seq call .skip)
      have ticksRun : DataSem.evaluate rest tmid = (none, targetNext) := by
        dsimp only [rest]
        rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
        exact seqRun
      have targetRun := evaluateSeq_continue argsProg rest t1 tmid _ target targetBound ticksRun
      refine ⟨wholeRun, targetNext, .seq argsProg rest, none,
        [n2], n2 + 1, none, ?_, targetRun, targetRel, ?_⟩
      · simp [compileSource, compiled, handlerCompiled, rest, call, roots]
      · exact correctOutcome_seq values (.val [value]) t1 tmid targetNext n n1 (n2 + 1)
          corr live argNames [n2] env false none ls none firstOutcome secondOutcome
    | true =>
      let finished := DataSem.flushState false targetNext
      have returnRun : DataSem.evaluate (.return [n2]) targetNext = (some (.val [dataValue]), finished) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead, finished]
      have seqRun : DataSem.evaluate (.seq call (.return [n2])) afterTicks = (some (.val [dataValue]), finished) :=
        evaluateSeq_continue call (.return [n2]) afterTicks targetNext _ callRun callBound returnRun
      let rest := DataLang.mkTicks ticks (.seq call (.return [n2]))
      have ticksRun : DataSem.evaluate rest tmid = (some (.val [dataValue]), finished) := by
        dsimp only [rest]
        rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
        exact seqRun
      have targetRun := evaluateSeq_continue argsProg rest t1 tmid _ target targetBound ticksRun
      have finalRel : stateRel s2 finished := by simpa [stateRel, finished, DataSem.flushState] using targetRel
      have returnedOutcome : correctOutcome (.val [value]) tmid finished n1 (n2 + 1) corr live [n2] env true
          (some (.val [dataValue])) none := by
        simp [correctOutcome, isReturn, isResult, isException, dataToBviResult, valueProjection,
          finished, DataSem.flushState, targetNext, restored, DataSem.setVar]
      refine ⟨wholeRun, finished, .seq argsProg rest, some (.val [dataValue]),
        [n2], n2 + 1, none, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, handlerCompiled, rest, call, roots]
      · exact correctOutcome_seq values (.val [value]) t1 tmid finished n n1 (n2 + 1)
          corr live argNames [n2] env true (some (.val [dataValue])) ls none firstOutcome returnedOutcome

/-- A direct handled call that exhausts its clock after evaluating arguments
times out before either its callee or handler runs. -/
theorem simulationFor_call_handler_timeout {C F : Type} (ticks dest : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, body))
    (timeout : smid.clock < ticks + 1)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks (some dest) args (some handler)] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, timeout]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    generalize handlerCompiled : compileSource (n1 + 1) (n1 :: corr) false live [handler] = triple
    obtain ⟨handlerProg, handlerNames, n2⟩ := triple
    let roots := live ++ corr
    let after := if tail then DataLang.Prog.return [n2] else .skip
    let call := DataLang.Prog.call (some ([n2], namesOfList roots)) (some dest) argNames
      (some (n1, .seq handlerProg (.move n2 (Flapjack.holHd handlerNames))))
    let rest := DataLang.mkTicks ticks (.seq call after)
    have targetTimeout : tmid.clock < ticks + 1 := by simpa [← middleRel.1] using timeout
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    by_cases before : tmid.clock < ticks
    · let last := { tmid with clock := 0, locals := .ln, stack := [], localsSize := some 0 }
      have restRun : DataSem.evaluate rest tmid = (some (.err (.abort .timeoutError)), last) := by
        simp [rest, DataSem.evaluate_mkTicks, before, last]
      have targetRun := evaluateSeq_continue argsProg rest t1 tmid _ target targetBound restRun
      have finalRel : stateRel { smid with clock := 0 } last := by
        simpa [stateRel, last] using middleRel.2
      refine ⟨wholeRun, last, .seq argsProg rest, some (.err (.abort .timeoutError)), [n2], n2 + 1,
        ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, handlerCompiled, rest, call, after, roots]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
    · have targetClock : tmid.clock = ticks := by omega
      have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
      have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
        intro key member
        exact liveMidAll key (List.mem_append_right argNames member)
      have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := outcome.2.2.2.2.1
      have resultVars : DataProps.varCorr values argNames (sptMap dataToBviValue tmid.locals) := outcome.2.2.2.2.2.2.2.2.2.2
      obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
      have projectedCode : BvlSem.findCode (some dest) (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
        simpa [← projected] using sourceCode
      obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
        findCode_direct smid tmid dest dataValues callArgs body middleRel projectedCode
      let afterTicks := { tmid with clock := tmid.clock - ticks }
      have afterClock : afterTicks.clock = 0 := by simp [afterTicks, targetClock]
      have afterRead : DataSem.getVars argNames afterTicks.locals = some dataValues := by simpa [afterTicks] using read
      have afterCode : DataSem.findCode (some dest) dataValues afterTicks.code afterTicks.stackFrameSizes =
          some (dataArgs, compileExp dataArgs.length body, size) := by simpa [afterTicks] using targetCode
      let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
      have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
        simpa [roots, DataSem.getVars] using
          (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
      have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
        cutEnv_namesOfList roots tmid.locals rootsPresent
      let callState := DataSem.callEnv dataArgs size (DataSem.pushEnv cut true (DataSem.decClock afterTicks))
      let last := { callState with stack := [], locals := .ln }
      have callRun : DataSem.evaluate call afterTicks = (some (.err (.abort .timeoutError)), last) := by
        simp [call, DataSem.evaluate, afterRead, afterCode, afterClock, cutEnv, callState, last]
      have lastClock : last.clock ≤ afterTicks.clock := by simp [last, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, afterClock]
      have seqRun : DataSem.evaluate (.seq call after) afterTicks = (some (.err (.abort .timeoutError)), last) :=
        evaluateSeq_stop call after afterTicks last _ callRun lastClock
      have restRun : DataSem.evaluate rest tmid = (some (.err (.abort .timeoutError)), last) := by
        dsimp only [rest]
        rw [DataSem.evaluate_mkTicks, if_neg before]
        exact seqRun
      have targetRun := evaluateSeq_continue argsProg rest t1 tmid _ target targetBound restRun
      have finalRel : stateRel { smid with clock := 0 } last := by
        simpa [stateRel, last, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, afterTicks, targetClock] using middleRel.2
      refine ⟨wholeRun, last, .seq argsProg rest, some (.err (.abort .timeoutError)), [n2], n2 + 1,
        ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, handlerCompiled, rest, call, after, roots]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- A handled call propagates a callee abort without running its handler. -/
theorem simulationFor_call_handler_abort {C F : Type} (ticks dest : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env values callArgs : List BvlSem.Value) (body : Bvi.Exp)
    (s1 smid s2 : BviSem.BviState C F) (error : Abort)
    (ihArgs : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, body))
    (clock : ticks + 1 ≤ smid.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = (.err (.abort error), s2))
    (notType : error ≠ .typeError)
    (ihBody : simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.err (.abort error), s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks (some dest) args (some handler)] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err (.abort error)) t1 t2 n next corr live names env tail pres ls := by
  have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
      (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (.err (.abort error), s2) := by
    rw [BviSem.fixClock_evaluate, bodyRun]
  have wholeRun : BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.err (.abort error), s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show ¬ smid.clock < ticks + 1 by omega, bodyClamped]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ihArgs (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    generalize handlerCompiled : compileSource (n1 + 1) (n1 :: corr) false live [handler] = triple
    obtain ⟨handlerProg, handlerNames, n2⟩ := triple
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
      intro key member
      exact liveMidAll key (List.mem_append_right argNames member)
    have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := outcome.2.2.2.2.1
    have resultVars : DataProps.varCorr values argNames (sptMap dataToBviValue tmid.locals) := outcome.2.2.2.2.2.2.2.2.2.2
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedCode : BvlSem.findCode (some dest) (dataValues.map dataToBviValue) smid.code = some (callArgs, body) := by
      simpa [← projected] using sourceCode
    obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
      findCode_direct smid tmid dest dataValues callArgs body middleRel projectedCode
    subst callArgs
    have targetClock : ticks + 1 ≤ tmid.clock := by simpa [← middleRel.1] using clock
    let afterTicks := { tmid with clock := tmid.clock - ticks }
    have positive : afterTicks.clock ≠ 0 := by simp only [afterTicks]; omega
    have afterRead : DataSem.getVars argNames afterTicks.locals = some dataValues := by simpa [afterTicks] using read
    have afterCode : DataSem.findCode (some dest) dataValues afterTicks.code afterTicks.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by simpa [afterTicks] using targetCode
    let roots := live ++ corr
    let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
    have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
      simpa [roots, DataSem.getVars] using
        (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
    have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
      cutEnv_namesOfList roots tmid.locals rootsPresent
    let pushed := DataSem.pushEnv cut true (DataSem.decClock afterTicks)
    have entryRel : stateRel (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) := by
      have entry := stateRel_callEntry smid tmid dataArgs size ticks middleRel
      simpa [stateRel, DataSem.callEnv, afterTicks] using entry
    have pushedRel := stateRel_pushEnv (BviSem.decClock (ticks + 1) smid) (DataSem.decClock afterTicks) cut true entryRel
    obtain ⟨result, final, bodyNames, next, lsBody, localsSize, stackMax, safe, peak, bodyTarget,
        finalRel, optimizedRel, bodyOutcome⟩ :=
      compileExp_callEnv body dataArgs (BviSem.decClock (ticks + 1) smid) s2 (.err (.abort error)) pushed size
        ihBody bodyRun (by simpa using notType) pushedRel (by simp [isException])
    have resultEq : result = .err (.abort error) := by
      have projection := bodyOutcome.1 (by simp [isReturn])
      cases result with
      | val values => simp [dataToBviResult] at projection
      | err failure => cases failure with
        | abort reason => simpa [dataToBviResult] using projection
        | raise value => simp [dataToBviResult] at projection
    subst result
    let optimized := { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
    have clamped : DataSem.fixClock (DataSem.callEnv dataArgs size pushed)
        (DataSem.evaluate (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)) =
        (some (.err (.abort error)), optimized) := by
      rw [DataSem.fixClock_evaluate, bodyTarget]
    let call := DataLang.Prog.call (some ([n2], namesOfList roots)) (some dest) argNames
      (some (n1, .seq handlerProg (.move n2 (Flapjack.holHd handlerNames))))
    let after := if tail then DataLang.Prog.return [n2] else .skip
    have callRun : DataSem.evaluate call afterTicks = (some (.err (.abort error)), optimized) := by
      simp only [call, DataSem.evaluate, afterRead, afterCode, List.nodup_singleton, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, cutEnv, positive, Option.isSome_some]
      rw [clamped]
    have bodyBound := DataSem.evaluate_clock_le (compileExp dataArgs.length body) (DataSem.callEnv dataArgs size pushed)
    rw [bodyTarget] at bodyBound
    have finalBound : optimized.clock ≤ afterTicks.clock := by
      simpa [optimized, DataSem.callEnv, pushed, DataSem.pushEnv, DataSem.decClock] using
        Nat.le_trans bodyBound (Nat.sub_le afterTicks.clock 1)
    have seqRun := evaluateSeq_stop call after afterTicks optimized (.err (.abort error)) callRun finalBound
    let rest := DataLang.mkTicks ticks (.seq call after)
    have ticksRun : DataSem.evaluate rest tmid = (some (.err (.abort error)), optimized) := by
      dsimp only [rest]
      rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
      exact seqRun
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have targetRun := evaluateSeq_continue argsProg rest t1 tmid _ target targetBound ticksRun
    refine ⟨wholeRun, optimized, .seq argsProg rest, some (.err (.abort error)), [n2], n2 + 1,
      lsBody, ?_, targetRun, optimizedRel, ?_⟩
    · simp [compileSource, compiled, handlerCompiled, rest, call, after, roots]
    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

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

/-- The unhandled-call expression simulation, assuming the evaluator's
recursive induction hypotheses for the arguments and the called body. -/
theorem simulationFor_call_noHandler {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (ihArgs : simulationFor args env source)
    (ihBody : ∀ values smid callArgs body,
      BviSem.evaluate args env source = (.val values, smid) →
      BvlSem.findCode dest values smid.code = some (callArgs, body) →
      ticks + 1 ≤ smid.clock → simulationFor [body] callArgs (BviSem.decClock (ticks + 1) smid)) :
    simulationFor [.call ticks dest args none] env source := by
  intro res s2 target n corr tail live run notType vars tailShape fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env source = argsPair
  obtain ⟨argsResult, smid⟩ := argsPair
  cases argsResult with
  | err error =>
    have whole : BviSem.evaluate [.call ticks dest args none] env source = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
      simp
    rw [whole] at run
    cases run
    exact (simulationFor_call_argsError ticks dest args env source s2 error ihArgs argsRun notType
      target n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    cases sourceCode : BvlSem.findCode dest values smid.code with
    | none =>
      have whole : BviSem.evaluate [.call ticks dest args none] env source = (.err (.abort .typeError), smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [sourceCode]
      rw [whole] at run
      cases run
      exact False.elim (notType rfl)
    | some pair =>
      obtain ⟨callArgs, body⟩ := pair
      by_cases timeout : smid.clock < ticks + 1
      · have simulated := simulationFor_call_timeout ticks dest args env values callArgs body source smid ihArgs
          argsRun sourceCode timeout target n corr tail live vars fresh related livePresent
        rw [simulated.1] at run
        cases run
        exact simulated.2
      · have clock : ticks + 1 ≤ smid.clock := by omega
        generalize bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid) = bodyPair
        obtain ⟨bodyResult, bodyState⟩ := bodyPair
        have bodyClamped : BviSem.fixClock (BviSem.decClock (ticks + 1) smid)
            (BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) smid)) = (bodyResult, bodyState) := by
          rw [BviSem.fixClock_evaluate, bodyRun]
        by_cases returns : isReturn bodyResult
        · obtain ⟨returned, rfl⟩ := returns
          have whole : BviSem.evaluate [.call ticks dest args none] env source = (.err (.abort .typeError), bodyState) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
            simp [sourceCode, timeout, bodyClamped]
          rw [whole] at run
          cases run
          exact False.elim (notType rfl)
        · have whole : BviSem.evaluate [.call ticks dest args none] env source = (bodyResult, bodyState) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
            simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, sourceCode, timeout, bodyClamped]
            cases bodyResult with
            | val resultValues => rfl
            | err error => cases error with
              | abort error => rfl
              | raise value => cases value with
                | exn value => rfl
                | ret values => exact False.elim (returns ⟨values, rfl⟩)
          rw [whole] at run
          cases run
          have bodyIH := ihBody values smid callArgs body argsRun sourceCode clock
          cases tail with
          | true =>
            exact (simulationFor_call_tail_recursive ticks dest args env values callArgs body source smid s2 res
              ihArgs argsRun sourceCode clock bodyRun returns notType bodyIH target n corr live vars fresh related livePresent exceptionJump).2
          | false =>
            cases res with
            | val resultValues =>
              obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton body callArgs (BviSem.decClock (ticks + 1) smid) s2 resultValues bodyRun
              exact (simulationFor_call_nontail_value ticks dest args env values callArgs body source smid s2 value
                ihArgs argsRun sourceCode clock bodyRun bodyIH target n corr live vars fresh related livePresent).2
            | err error => cases error with
              | abort error =>
                exact (simulationFor_call_nontail_abort ticks dest args env values callArgs body source smid s2 error
                  ihArgs argsRun sourceCode clock bodyRun (by simpa using notType) bodyIH target n corr live vars fresh related livePresent).2
              | raise value => cases value with
                | exn value =>
                  exact (simulationFor_call_nontail_exception ticks dest args env values callArgs body source smid s2 value
                    ihArgs argsRun sourceCode clock bodyRun bodyIH target n corr live vars fresh related livePresent
                    (exceptionJump (by simp [isException]))).2
                | ret values => exact False.elim (returns ⟨values, rfl⟩)

end Flapjack.Compiler.Backend.BviToData
