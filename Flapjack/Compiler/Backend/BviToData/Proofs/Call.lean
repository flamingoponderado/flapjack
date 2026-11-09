module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.BviToData.Proofs.Optimise
public import Flapjack.Compiler.Backend.BviToData.Proofs.FindCode
public import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
public import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
public import Flapjack.Compiler.Backend.Semantics.DataProps.Ticks
public import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateForce
public import Flapjack.Misc.Sptree.UnionAlgebra
public import Mathlib.Data.List.Induction

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Call argument cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem setVars_singleton {C F : Type} (name : Nat) (value : DataSem.Value) (state : DataSem.State C F) :
    DataSem.setVars [name] [value] state = DataSem.setVar name value state := by
  simp [DataSem.setVars, DataSem.setVar, sptFromAList, sptUnion_insert_ln]

/-- Changing distinct result locals does not affect a non-type-error call
failure: the result locals are used only after a successful callee return. -/
theorem evaluate_call_changeReturns_failure {C F : Type} (names1 names2 : List Nat)
    (roots : NumSet) (dest : Option Nat) (args : List Nat)
    (state last : DataSem.State C F) (error : ErrorResult DataSem.Value)
    (distinct1 : names1.Nodup) (distinct2 : names2.Nodup)
    (notType : error ≠ .abort .typeError)
    (run : DataSem.evaluate (.call (some (names1, roots)) dest args none) state = (some (.err error), last)) :
    DataSem.evaluate (.call (some (names2, roots)) dest args none) state = (some (.err error), last) := by
  cases read : DataSem.getVars args state.locals with
  | none => simp [DataSem.evaluate, read] at run; exact False.elim (notType run.1.symm)
  | some values =>
    cases code : DataSem.findCode dest values state.code state.stackFrameSizes with
    | none => simp [DataSem.evaluate, read, code] at run; exact False.elim (notType run.1.symm)
    | some entry =>
      obtain ⟨callArgs, body, size⟩ := entry
      cases cut : DataSem.cutEnv roots state.locals with
      | none => simp [DataSem.evaluate, read, code, distinct1, cut] at run; exact False.elim (notType run.1.symm)
      | some saved =>
        by_cases clock : state.clock = 0
        · simpa [DataSem.evaluate, read, code, distinct1, distinct2, cut, clock] using run
        · let entered := DataSem.callEnv callArgs size (DataSem.pushEnv saved false (DataSem.decClock state))
          generalize bodyRun : DataSem.fixClock entered (DataSem.evaluate body entered) = bodyPair
          obtain ⟨bodyResult, bodyState⟩ := bodyPair
          have actualBody : DataSem.fixClock (DataSem.callEnv callArgs size (DataSem.pushEnv saved false (DataSem.decClock state)))
              (DataSem.evaluate body (DataSem.callEnv callArgs size (DataSem.pushEnv saved false (DataSem.decClock state)))) =
              (bodyResult, bodyState) := bodyRun
          cases bodyResult with
          | none =>
            simp [DataSem.evaluate, read, code, distinct1, cut, clock, actualBody] at run
            exact False.elim (notType run.1.symm)
          | some result =>
            cases result with
            | val values =>
              by_cases length : values.length = names1.length
              · cases pop : DataSem.popEnv bodyState with
                | none =>
                  simp [DataSem.evaluate, read, code, distinct1, cut, clock, actualBody, length, pop] at run
                  exact False.elim (notType run.1.symm)
                | some restored =>
                  simp [DataSem.evaluate, read, code, distinct1, cut, clock, actualBody, length, pop] at run
              · simp [DataSem.evaluate, read, code, distinct1, cut, clock, actualBody, length] at run
                exact False.elim (notType run.1.symm)
            | err failure =>
              cases failure <;>
                simpa [DataSem.evaluate, read, code, distinct1, distinct2, cut, clock, actualBody] using run

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

private theorem evaluate_vars_of_relation {C F : Type} (indices : List Nat) (values env : List BvlSem.Value)
    (state : BviSem.BviState C F)
    (lookups : List.Forall₂ (fun index value => env[index]? = some value) indices values) :
    BviSem.evaluate (indices.map Bvi.Exp.var) env state = (.val values, state) := by
  induction lookups with
  | nil => simp [BviSem.evaluate]
  | @cons index value indices values lookup rest ih =>
    cases indices with
    | nil =>
      cases rest
      simp [BviSem.evaluate, lookup]
    | cons second more =>
      rw [List.map_cons, List.map_cons, BviSem.evaluate, BviSem.fixClock_evaluate]
      simp only [List.map_cons] at ih
      simp [BviSem.evaluate, lookup, ih]
      rfl

/-- Returning the first `rets` environment values forwards exactly those
values. This is the local source lemma used by the let-call tail rewrite;
the evaluator correspondence remains under review. -/
theorem evaluate_return_range {C F : Type} (rets : Nat) (values env : List BvlSem.Value)
    (state : BviSem.BviState C F) (length : values.length = rets) :
    BviSem.evaluate [.return ((List.range rets).map Bvi.Exp.var)] (values ++ env) state =
      (.err (.raise (.ret values)), state) := by
  have lookups : List.Forall₂ (fun index value => (values ++ env)[index]? = some value) (List.range rets) values := by
    apply List.forall₂_iff_get.mpr
    constructor
    · simp [length]
    · intro index leftBound rightBound
      have bound : index < values.length := rightBound
      simp [List.getElem?_append, bound]
  have evaluated := evaluate_vars_of_relation (List.range rets) values (values ++ env) state lookups
  simp [BviSem.evaluate, evaluated]

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

/-- The contiguous return-name association list looks up exactly the value
at the corresponding offset. -/
theorem lookup_return_bindings {α : Type} (values : List α) (start key : Nat) :
    sptLookup key (sptFromAList (((List.range values.length).map (start + ·)).zip values)) =
      if start ≤ key then values[key - start]? else none := by
  rw [← List.range'_eq_map_range, sptLookup_sptFromAList]
  induction values generalizing start key with
  | nil => simp [sptAListLookup]
  | cons value values ih =>
    simp only [List.length_cons, List.range', List.zip_cons_cons, sptAListLookup]
    by_cases equal : key = start
    · subst key
      simp
    · rw [if_neg equal]
      rw [ih]
      by_cases before : key < start
      · simp [show ¬ start ≤ key by omega, show ¬ start + 1 ≤ key by omega]
      · have later : start + 1 ≤ key := by omega
        have diff : key - start = (key - (start + 1)) + 1 := by omega
        simp [show start ≤ key by omega, later, diff]

/-- Installing consecutive returned values reads the new binding at an
in-range offset and otherwise retains the previous local. -/
theorem lookup_setVars_returns {C F : Type} (values : List DataSem.Value)
    (start key : Nat) (state : DataSem.State C F) :
    sptLookup key (DataSem.setVars ((List.range values.length).map (start + ·)) values state).locals =
      (if start ≤ key then values[key - start]? else none).orElse (fun _ => sptLookup key state.locals) := by
  simp only [DataSem.setVars, sptLookup_sptUnion, lookup_return_bindings]
  generalize h : (if start ≤ key then values[key - start]? else none) = found
  cases found <;> rfl

/-- Installing a complete returned-value list into fresh consecutive locals
establishes the binding invariant needed by the let-call continuation. -/
theorem correctOutcome_returns_entry {C F : Type} (target restored : DataSem.State C F)
    (n : Nat) (corr live : List Nat) (env values : List BvlSem.Value) (dataValues : List DataSem.Value)
    (projected : values = dataValues.map dataToBviValue)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (locals : restored.locals = sptMkWf (sptInter target.locals (namesOfList (live ++ corr))))
    (stack : restored.stack = target.stack) (handler : restored.handler = target.handler) :
    correctOutcome (.val values) target
      (DataSem.setVars ((List.range dataValues.length).map (n + ·)) dataValues restored)
      n (n + dataValues.length) corr live ((List.range dataValues.length).map (n + ·)) env false none none := by
  let roots := live ++ corr
  let next := DataSem.setVars ((List.range dataValues.length).map (n + ·)) dataValues restored
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
    simpa [roots, DataSem.getVars] using
      (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
  have oldRead : ∀ key, key < n → sptLookup key next.locals =
      if key ∈ roots then sptLookup key target.locals else none := by
    intro key bound
    rw [show sptLookup key next.locals = _ from lookup_setVars_returns dataValues n key restored]
    simp only [show ¬ n ≤ key by omega, ↓reduceIte]
    rw [locals]
    exact lookup_cut_namesOfList roots target.locals key
  have newRead : ∀ index (bound : index < dataValues.length),
      sptLookup (n + index) next.locals = some dataValues[index] := by
    intro index bound
    rw [show sptLookup (n + index) next.locals = _ from lookup_setVars_returns dataValues n (n + index) restored]
    simp [List.getElem?_eq_getElem bound]
  have highRead : ∀ key, n + dataValues.length ≤ key → sptLookup key next.locals = none := by
    intro key bound
    rw [show sptLookup key next.locals = _ from lookup_setVars_returns dataValues n key restored]
    have outside : dataValues[key - n]? = none := List.getElem?_eq_none (by omega)
    simp only [show n ≤ key by omega, ↓reduceIte, outside]
    rw [locals, lookup_cut_namesOfList roots target.locals key]
    simp [fresh key (by omega)]
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue next.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals next.locals corr env vars
    intro key member
    have root : key ∈ roots := by simp [roots, member]
    have below : key < n := by
      by_contra bound
      exact rootsPresent key root (fresh key (by omega))
    rw [oldRead key below, if_pos root]
  have valueVars : DataProps.varCorr values ((List.range dataValues.length).map (n + ·))
      (sptMap dataToBviValue next.locals) := by
    subst values
    apply List.forall₂_iff_get.mpr
    constructor
    · simp
    · intro index leftBound rightBound
      have bound : index < dataValues.length := by simpa using rightBound
      simp [DataSem.getVar, sptLookup_sptMap, newRead index bound]
  change correctOutcome (.val values) target next n (n + dataValues.length) corr live
    ((List.range dataValues.length).map (n + ·)) env false none none
  simp only [correctOutcome, true_and]
  refine ⟨by omega, ?_, highRead, varsNew, ?_, ?_, ?_, ?_, ?_, valueVars⟩
  · intro key member
    simp only [List.mem_map, List.mem_range] at member
    obtain ⟨index, bound, rfl⟩ := member
    omega
  · intro key value lookup
    by_contra bound
    have absent := highRead key (by omega)
    rw [lookup] at absent
    contradiction
  · intro key value lookup needed
    have below : key < n := by
      by_contra bound
      have absent := fresh key (by omega)
      rw [lookup] at absent
      contradiction
    have root : key ∈ roots := by
      by_cases member : key ∈ live
      · simp [roots, member]
      · simp [roots, needed member]
    rw [oldRead key below, if_pos root]
    exact lookup
  · simp [next, DataSem.setVars, stack]
  · simp [next, DataSem.setVars, handler]
  · intro available
    cases old : DataSem.jumpExc target with
    | none => exact False.elim (available old)
    | some jumped =>
      have moved := DataSem.jumpExc_transport target next jumped
        (by simp [next, DataSem.setVars, stack]) (by simp [next, DataSem.setVars, handler]) old
      rw [moved]
      simp

/-- After restoring a caller frame and binding all returned values, run the
recursively simulated let-call continuation and discharge its local-binding
obligations back to the caller's environment. -/
theorem simulationFor_returned_continuation {C F : Type} (body : Bvi.Exp)
    (env values : List BvlSem.Value) (dataValues : List DataSem.Value)
    (source nextSource : BviSem.BviState C F) (res : BviSem.BviResult)
    (target restored : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (ih : simulationFor [body] (values ++ env) source)
    (run : BviSem.evaluate [body] (values ++ env) source = (res, nextSource))
    (notType : res ≠ .err (.abort .typeError))
    (projected : values = dataValues.map dataToBviValue)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (locals : restored.locals = sptMkWf (sptInter target.locals (namesOfList (live ++ corr))))
    (stack : restored.stack = target.stack) (handler : restored.handler = target.handler)
    (related : stateRel source restored)
    (exceptionJump : isException res → DataSem.jumpExc target ≠ none) :
    ∃ prog names next targetNext pres ls,
      compileSource (n + dataValues.length) (((List.range dataValues.length).map (n + ·)) ++ corr) tail live [body] = (prog, names, next) ∧
      DataSem.evaluate prog (DataSem.setVars ((List.range dataValues.length).map (n + ·)) dataValues restored) = (pres, targetNext) ∧
      stateRel nextSource targetNext ∧
      correctOutcome res target targetNext n next corr live names env tail pres ls := by
  let returns := (List.range dataValues.length).map (n + ·)
  let start := DataSem.setVars returns dataValues restored
  have base : correctOutcome (.val values) target start n (n + dataValues.length) corr live returns env false none none :=
    correctOutcome_returns_entry target restored n corr live env values dataValues projected vars fresh livePresent locals stack handler
  have startRel : stateRel source start := by simpa [start, DataSem.setVars, stateRel] using related
  have liveAll := correctOutcome_live values target start n (n + dataValues.length) corr live returns env none base livePresent
  have liveStart : ∀ key ∈ live, sptLookup key start.locals ≠ none := by
    intro key member
    exact liveAll key (List.mem_append_right returns member)
  have freshStart : ∀ key, n + dataValues.length ≤ key → sptLookup key start.locals = none := base.2.2.2.1
  have oldVars : DataProps.varCorr env corr (sptMap dataToBviValue start.locals) := base.2.2.2.2.1
  have valueVars : DataProps.varCorr values returns (sptMap dataToBviValue start.locals) := base.2.2.2.2.2.2.2.2.2.2
  have bodyVars : DataProps.varCorr (values ++ env) (returns ++ corr) (sptMap dataToBviValue start.locals) :=
    List.rel_append valueVars oldVars
  have jumpStart : isException res → DataSem.jumpExc start ≠ none := by
    intro exception
    exact base.2.2.2.2.2.2.2.2.2.1 (exceptionJump exception)
  obtain ⟨final, prog, pres, names, next, ls, compiled, targetRun, finalRel, outcome⟩ :=
    ih res nextSource start (n + dataValues.length) (returns ++ corr) tail live run notType bodyVars
      (by simp) freshStart startRel liveStart jumpStart
  refine ⟨prog, names, next, final, pres, ls, compiled, targetRun, finalRel, ?_⟩
  exact correctOutcome_let values res target start final n (n + dataValues.length) next corr live returns names
    env tail pres none ls base outcome

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

/-- A let-call times out during its generated ticks before the callee or
continuation is reached, for either compiler rewrite. -/
theorem simulationFor_letCall_ticksTimeout {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env values callArgs : List BvlSem.Value) (callee : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, callee))
    (timeout : smid.clock < ticks)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.letCall rets ticks dest args body] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.letCall rets ticks dest args body] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  classical
  have sourceRun : BviSem.evaluate [.letCall rets ticks dest args body] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, show smid.clock < ticks + 1 by omega]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have targetTimeout : tmid.clock < ticks := by simpa [← middleRel.1] using timeout
    let last := { tmid with clock := 0, locals := .ln, stack := [], localsSize := some 0 }
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have finalRel : stateRel { smid with clock := 0 } last := by simpa [stateRel, last] using middleRel.2
    by_cases identity : body = .return ((List.range rets).map Bvi.Exp.var)
    · let rest := DataLang.mkTicks ticks (.call none (some dest) argNames none)
      have restRun : DataSem.evaluate rest tmid = (some (.err (.abort .timeoutError)), last) := by
        simp [rest, DataSem.evaluate_mkTicks, targetTimeout, last]
      have targetRun := evaluateSeq_continue argsProg rest t1 tmid _ target targetBound restRun
      refine ⟨sourceRun, last, .seq argsProg rest, some (.err (.abort .timeoutError)), [n1], n1 + 1,
        ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, rest]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
    · let returns := (List.range rets).map (n1 + ·)
      generalize bodyCompiled : compileSource (n1 + rets) (returns ++ corr) tail live [body] = triple
      obtain ⟨bodyProg, bodyNames, n2⟩ := triple
      let rest := DataLang.mkTicks ticks (.call (some (returns, namesOfList (live ++ corr))) (some dest) argNames none)
      let inner := DataLang.Prog.seq argsProg rest
      have restRun : DataSem.evaluate rest tmid = (some (.err (.abort .timeoutError)), last) := by
        simp [rest, DataSem.evaluate_mkTicks, targetTimeout, last]
      have innerRun : DataSem.evaluate inner t1 = (some (.err (.abort .timeoutError)), last) :=
        evaluateSeq_continue argsProg rest t1 tmid _ target targetBound restRun
      have lastBound : last.clock ≤ t1.clock := by simp [last]
      have targetRun := evaluateSeq_stop inner bodyProg t1 last (.err (.abort .timeoutError)) innerRun lastBound
      refine ⟨sourceRun, last, .seq inner bodyProg, some (.err (.abort .timeoutError)), bodyNames, n2,
        ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, bodyCompiled, inner, rest, returns]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- The let-call tail rewrite shares the ordinary tail call's timeout path. -/
theorem simulationFor_letCall_tailRewrite_timeout {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (env values callArgs : List BvlSem.Value) (callee : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, callee))
    (timeout : smid.clock < ticks + 1)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.letCall rets ticks dest args (.return ((List.range rets).map Bvi.Exp.var))] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.letCall rets ticks dest args (.return ((List.range rets).map Bvi.Exp.var))] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  have sourceRun : BviSem.evaluate [.letCall rets ticks dest args (.return ((List.range rets).map Bvi.Exp.var))] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [sourceCode, timeout]
  obtain ⟨_, t2, prog, pres, names, next, ls, compiled, target, finalRel, outcome⟩ :=
    simulationFor_call_timeout ticks (some dest) args env values callArgs callee s1 smid ih argsRun sourceCode timeout
      t1 n corr true live vars fresh related livePresent
  have sameCompile : compileSource n corr tail live [.letCall rets ticks dest args (.return ((List.range rets).map Bvi.Exp.var))] =
      compileSource n corr true live [.call ticks (some dest) args none] := by
    simp [compileSource]
  refine ⟨sourceRun, t2, prog, pres, names, next, ls, sameCompile.trans compiled, target, finalRel, ?_⟩
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result => simpa [correctOutcome, isResult] using outcome

/-- A let-call also times out at call entry when its generated ticks consume
exactly the available clock, including the multi-result continuation form. -/
theorem simulationFor_letCall_entryTimeout {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env values callArgs : List BvlSem.Value) (callee : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, callee))
    (timeout : smid.clock = ticks)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.letCall rets ticks dest args body] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.letCall rets ticks dest args body] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  classical
  by_cases identity : body = .return ((List.range rets).map Bvi.Exp.var)
  · subst body
    exact simulationFor_letCall_tailRewrite_timeout rets ticks dest args env values callArgs callee s1 smid ih
      argsRun sourceCode (by omega) t1 n corr tail live vars fresh related livePresent
  · have sourceRun : BviSem.evaluate [.letCall rets ticks dest args body] env s1 =
        (.err (.abort .timeoutError), { smid with clock := 0 }) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
      simp [sourceCode, timeout]
    obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
      ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent (by simp [isException])
    cases pres with
    | some result => simp [correctOutcome, isResult] at outcome
    | none =>
      have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
      have liveMid : ∀ key ∈ live, sptLookup key tmid.locals ≠ none := by
        intro key member
        exact liveMidAll key (List.mem_append_right argNames member)
      have varsMid : DataProps.varCorr env corr (sptMap dataToBviValue tmid.locals) := outcome.2.2.2.2.1
      have resultVars : DataProps.varCorr values argNames (sptMap dataToBviValue tmid.locals) := outcome.2.2.2.2.2.2.2.2.2.2
      obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
      have projectedCode : BvlSem.findCode (some dest) (dataValues.map dataToBviValue) smid.code = some (callArgs, callee) := by
        simpa [← projected] using sourceCode
      obtain ⟨dataArgs, size, argsProjection, targetCode⟩ :=
        findCode_direct smid tmid dest dataValues callArgs callee middleRel projectedCode
      have targetClock : tmid.clock = ticks := by simpa [← middleRel.1] using timeout
      let afterTicks := { tmid with clock := tmid.clock - ticks }
      have afterClock : afterTicks.clock = 0 := by simp [afterTicks, targetClock]
      have afterRead : DataSem.getVars argNames afterTicks.locals = some dataValues := by simpa [afterTicks] using read
      have afterCode : DataSem.findCode (some dest) dataValues afterTicks.code afterTicks.stackFrameSizes =
          some (dataArgs, compileExp dataArgs.length callee, size) := by simpa [afterTicks] using targetCode
      let roots := live ++ corr
      let cut := sptMkWf (sptInter tmid.locals (namesOfList roots))
      have rootsPresent : ∀ key ∈ roots, sptLookup key tmid.locals ≠ none := by
        simpa [roots, DataSem.getVars] using
          (roots_present tmid [] live corr env [] varsMid liveMid (by simp [DataSem.getVars]))
      have cutEnv : DataSem.cutEnv (namesOfList roots) afterTicks.locals = some cut :=
        cutEnv_namesOfList roots tmid.locals rootsPresent
      let returns := (List.range rets).map (n1 + ·)
      have distinct : returns.Nodup := by
        apply List.Nodup.map _ List.nodup_range
        intro a b equal
        exact Nat.add_left_cancel equal
      generalize bodyCompiled : compileSource (n1 + rets) (returns ++ corr) tail live [body] = triple
      obtain ⟨bodyProg, bodyNames, n2⟩ := triple
      let call := DataLang.Prog.call (some (returns, namesOfList roots)) (some dest) argNames none
      let callState := DataSem.callEnv dataArgs size (DataSem.pushEnv cut false (DataSem.decClock afterTicks))
      let last := { callState with stack := [], locals := .ln }
      have callRun : DataSem.evaluate call afterTicks = (some (.err (.abort .timeoutError)), last) := by
        simp [call, DataSem.evaluate, afterRead, afterCode, afterClock, distinct, cutEnv, callState, last]
      let rest := DataLang.mkTicks ticks call
      have restRun : DataSem.evaluate rest tmid = (some (.err (.abort .timeoutError)), last) := by
        dsimp only [rest]
        rw [DataSem.evaluate_mkTicks, if_neg (by omega : ¬ tmid.clock < ticks)]
        exact callRun
      have sourceBound := BviSem.evaluate_clock_le args env s1
      rw [argsRun] at sourceBound
      have targetBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
      let inner := DataLang.Prog.seq argsProg rest
      have innerRun : DataSem.evaluate inner t1 = (some (.err (.abort .timeoutError)), last) :=
        evaluateSeq_continue argsProg rest t1 tmid _ target targetBound restRun
      have lastBound : last.clock ≤ t1.clock := by
        simp [last, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, afterClock]
      have targetRun := evaluateSeq_stop inner bodyProg t1 last (.err (.abort .timeoutError)) innerRun lastBound
      have finalRel : stateRel { smid with clock := 0 } last := by
        simpa [stateRel, last, callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock, afterTicks, targetClock] using middleRel.2
      refine ⟨sourceRun, last, .seq inner bodyProg, some (.err (.abort .timeoutError)), bodyNames, n2,
        ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, bodyCompiled, inner, rest, call, roots, returns]
      · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]

/-- All post-argument let-call timeout cases, for either compilation form. -/
theorem simulationFor_letCall_timeout {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env values callArgs : List BvlSem.Value) (callee : Bvi.Exp)
    (s1 smid : BviSem.BviState C F) (ih : simulationFor args env s1)
    (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (sourceCode : BvlSem.findCode (some dest) values smid.code = some (callArgs, callee))
    (timeout : smid.clock < ticks + 1)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.letCall rets ticks dest args body] env s1 =
      (.err (.abort .timeoutError), { smid with clock := 0 }) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.letCall rets ticks dest args body] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel { smid with clock := 0 } t2 ∧
      correctOutcome (.err (.abort .timeoutError)) t1 t2 n next corr live names env tail pres ls := by
  by_cases before : smid.clock < ticks
  · exact simulationFor_letCall_ticksTimeout rets ticks dest args body env values callArgs callee s1 smid ih
      argsRun sourceCode before t1 n corr tail live vars fresh related livePresent
  · exact simulationFor_letCall_entryTimeout rets ticks dest args body env values callArgs callee s1 smid ih
      argsRun sourceCode (by omega) t1 n corr tail live vars fresh related livePresent

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
