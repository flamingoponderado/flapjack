module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallStep

@[expose] public section

/-! Closure-state relation for changing the compiler-oracle configuration. -/
namespace Flapjack.Compiler.Backend.ClosProps.AdjustOracle
open ClosSem BackendProps
open Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Two closure states differ only by a mapped compiler configuration and
compatible compilation callbacks. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "adj_orac_rel_def"
  (fmap_as_finite_support := [refs, code])]
def adjOracRel {C D F : Type} (cc : Compiler D) (f : C → D)
    (s : State C F) (t : State D F) : Prop :=
  (∀ n x y, s.compileOracle n = (x, y) →
    (s.compile x y).map (fun (bytes, words, cfg) => (bytes, words, f cfg)) = cc (f x) y) ∧
  t = ⟨s.globals, s.refs, s.ffi, s.clock, cc,
    (fun n => (f (s.compileOracle n).1, (s.compileOracle n).2)), s.code, s.maxApp⟩

private theorem forallEqRefl {A : Type} (xs : List A) : List.Forall₂ Eq xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

private theorem forallEqEqual {A : Type} {xs ys : List A} (h : List.Forall₂ Eq xs ys) : xs = ys := by
  induction h with
  | nil => rfl
  | cons head tail ih => cases head; simp [ih]

/-- Equality is a simple closure-value relation. This helper supports the
source oracle-adjustment simulation. -/
theorem simpleValRelEq : simpleValRel Eq := by
  simp only [simpleValRel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; trivial
  · intro x p n
    constructor
    · intro h; subst x; exact ⟨p, rfl, forallEqRefl _⟩
    · rintro ⟨xs, rfl, rel⟩
      have same : xs = p := forallEqEqual rel
      subst xs; rfl
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro body arity env args loc x h; subst x; trivial
  · intro index funs env args loc x h; subst x; trivial

/-- The source relation supports all primitive state updates. This is
Lean-side infrastructure for the source oracle-adjustment theorem. -/
theorem adjOracRel_simpleStateRel {C D F : Type} (cc : Compiler D) (f : C → D) :
    simpleStateRel Eq (adjOracRel (F := F) cc f) := by
  simp only [simpleStateRel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact missing
  · intro bytes t s ptr ⟨found, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact found
  · intro values t s ptr ⟨found, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact ⟨values, found, forallEqRefl _⟩
  · intro mode value t s ptr ⟨found, rel⟩
    rcases rel with ⟨_, rfl⟩
    exact ⟨value, found, rfl⟩
  · intro s t rel
    rcases rel with ⟨_, rfl⟩
    refine ⟨rfl, by simp, ?_⟩
    induction s.globals with
    | nil => exact .nil
    | cons a rest ih =>
      apply List.Forall₂.cons ?_ ih
      cases a <;> simp [optionRel]
  · intro ffi s t rel
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro bytes s t ptr rel
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro s t ptr xs ys ⟨rel, values⟩
    have equal := forallEqEqual values
    subst ys
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro s t ptr mode v w ⟨rel, equal⟩
    subst w
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩
  · intro s t xs ys ⟨rel, values⟩
    have equal : xs = ys := by
      induction values with
      | nil => rfl
      | @cons x y xs ys h tail ih =>
        cases x <;> cases y <;> simp_all [optionRel]
    subst ys
    rcases rel with ⟨compiler, rfl⟩
    exact ⟨compiler, rfl⟩

/-- A primitive error is unchanged by an oracle adjustment. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_adj_orac_Rerr"
  (fmap_as_finite_support := [refs, code])]
theorem doAppAdjOracErr {C D F : Type} (cc : Compiler D) (f : C → D)
    (op : ClosLang.Op) (xs : List Value) (s : State C F) (t : State D F)
    (err : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (h : doApp op xs s = .err err ∧ adjOracRel cc f s t) :
    doApp op xs t = .err err := by
  obtain ⟨run, rel⟩ := h
  have sim := PrimitiveTotal.simpleValRelDoApp Eq (adjOracRel cc f) s t xs xs op
    ⟨simpleValRelEq, adjOracRel_simpleStateRel cc f⟩ ⟨rel, forallEqRefl xs⟩
  rw [run] at sim
  obtain ⟨err', result, related⟩ := sim
  have same : err = err' := by cases err <;> cases err' <;> simp_all [excRel]
  simpa [← same] using result

/-- A successful primitive result is unchanged and its final states remain
related after an oracle adjustment. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_adj_orac_Rval"
  (fmap_as_finite_support := [refs, code])]
theorem doAppAdjOracVal {C D F : Type} (cc : Compiler D) (f : C → D)
    (op : ClosLang.Op) (xs : List Value) (s : State C F) (t : State D F)
    (value : Value) (next : State C F)
    (h : doApp op xs s = .val (value, next) ∧ adjOracRel cc f s t) :
    ∃ target, doApp op xs t = .val (value, target) ∧ adjOracRel cc f next target := by
  obtain ⟨run, rel⟩ := h
  have sim := PrimitiveTotal.simpleValRelDoApp Eq (adjOracRel cc f) s t xs xs op
    ⟨simpleValRelEq, adjOracRel_simpleStateRel cc f⟩ ⟨rel, forallEqRefl xs⟩
  rw [run] at sim
  obtain ⟨y, target, same, related, result⟩ := sim
  subst y
  exact ⟨target, result, related⟩

/-- A non-type-error dynamic installation produces the same result and
preserves the adjusted compiler-oracle relation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_install_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem doInstallAdjOrac {C D F : Type} (cc : Compiler D) (f : C → D)
    (xs : List Value) (s : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value)
    (next : State C F) (t : State D F)
    (h : doInstall xs s = (result, next) ∧ adjOracRel cc f s t ∧
      result ≠ .err (.abort .typeError)) :
    ∃ target, doInstall xs t = (result, target) ∧ adjOracRel cc f next target := by
  classical
  obtain ⟨run, ⟨compatible, rfl⟩, noType⟩ := h
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valuesEq, bytesRun, wordsRun, oracleRun, compileRun, fresh, nodup, nextConfigEq,
    nonempty, nextEq, resultEq⟩ := doInstall_nonType_parts xs s next result run noType
  subst xs
  let target : State D F := ⟨s.globals, s.refs, s.ffi, s.clock, cc,
    (fun n => (f (s.compileOracle n).1, (s.compileOracle n).2)), s.code, s.maxApp⟩
  have targetOracle : target.compileOracle 0 = (f config, expressions, auxiliary) := by
    simp [target, oracleRun]
  have targetCompile : cc (f config) (expressions, auxiliary) = some (bytes, words, f nextConfig) := by
    have h := compatible 0 config (expressions, auxiliary) oracleRun
    simpa [compileRun] using h.symm
  have targetConfig : (Flapjack.holShiftSeq 1 target.compileOracle 0).1 = f nextConfig := by
    simpa [target, Flapjack.holShiftSeq] using congrArg f nextConfigEq
  let nextTarget := { target with
    code := target.code.updateListEq auxiliary
    compileOracle := Flapjack.holShiftSeq 1 target.compileOracle
    clock := target.clock - 1 }
  refine ⟨nextTarget, ?_, ?_⟩
  · rw [resultEq]
    change doInstall [byteValue, wordValue] target = (_, nextTarget)
    have targetFresh : ∀ key arity body, (key, arity, body) ∈ auxiliary → target.code.lookup key = none := by
      intro key arity body member
      apply fresh key
      exact List.mem_map.mpr ⟨(key, arity, body), member, rfl⟩
    have targetCompile' : target.compile (f config) (expressions, auxiliary) =
        some (bytes, words, f nextConfig) := targetCompile
    by_cases zero : s.clock = 0
    · have targetZero : target.clock = 0 := by simpa [target] using zero
      simp [doInstall, bytesRun, wordsRun, targetOracle, nodup,
        targetConfig, nonempty, zero, targetZero, nextTarget]
      simp [targetCompile']
      exact targetFresh
    · have targetNonzero : target.clock ≠ 0 := by simpa [target] using zero
      simp [doInstall, bytesRun, wordsRun, targetOracle, nodup,
        targetConfig, nonempty, zero, targetNonzero, nextTarget]
      simp [targetCompile']
      exact targetFresh
  · rw [nextEq]
    constructor
    · intro n x y eq
      exact compatible (n + 1) x y (by simpa [Flapjack.holShiftSeq] using eq)
    · simp only [target, nextTarget, Flapjack.holShiftSeq]
      congr 1

/-- Fixed-input evaluator simulation used to state the source theorem's
structural induction hypotheses. -/
def EvalAt {C D F : Type} (cc : Compiler D) (f : C → D)
    (expressions : List ClosLang.Exp) (env : List Value) (s : State C F) : Prop :=
  ∀ result next (t : State D F),
    evaluate expressions env s = (result, next) ∧
    result ≠ .err (.abort .typeError) ∧ adjOracRel cc f s t →
    ∃ target, evaluate expressions env t = (result, target) ∧ adjOracRel cc f next target

/-- Fixed-input closure-application simulation for the mutual induction. -/
def AppAt {C D F : Type} (cc : Compiler D) (f : C → D)
    (location : Option Nat) (function : Value) (args : List Value) (s : State C F) : Prop :=
  ∀ result next (t : State D F),
    evaluateApp location function args s = (result, next) ∧
    result ≠ .err (.abort .typeError) ∧ adjOracRel cc f s t →
    ∃ target, evaluateApp location function args t = (result, target) ∧ adjOracRel cc f next target

/-- Empty-list case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracNil {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (env : List Value) (s : State C F) : EvalAt cc f [] env s := by
  intro result next t ⟨run, _, rel⟩
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨t, by simp [evaluate], rel⟩

/-- Variable case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracVar {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (index : Nat) (env : List Value) (s : State C F) :
    EvalAt cc f [.var trace index] env s := by
  intro result next t ⟨run, _, rel⟩
  cases found : env[index]? <;> simp [evaluate, found] at run
  all_goals obtain ⟨rfl, rfl⟩ := run
  all_goals exact ⟨t, by simp [evaluate, found], rel⟩

/-- Closure-construction case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracFn {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (name : Basis.Pure.MlString.MlString) (loc : Option Nat) (selected : Option (List Nat))
    (arity : Nat) (body : ClosLang.Exp) (env : List Value) (s : State C F) :
    EvalAt cc f [.fn name loc selected arity body] env s := by
  intro result next t ⟨run, _, rel⟩
  have maxEq : t.maxApp = s.maxApp := by rcases rel with ⟨_, rfl⟩; rfl
  by_cases valid : arity ≤ s.maxApp ∧ arity ≠ 0
  · cases selected with
    | none =>
      simp [evaluate, valid] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨t, by simp [evaluate, maxEq, valid], rel⟩
    | some indices =>
      cases capture : lookupVars indices env <;> simp [evaluate, valid, capture] at run
      all_goals obtain ⟨rfl, rfl⟩ := run
      all_goals exact ⟨t, by simp [evaluate, maxEq, valid, capture], rel⟩
  · cases selected <;> simp [evaluate, valid] at run
    all_goals obtain ⟨rfl, rfl⟩ := run
    all_goals exact ⟨t, by simp [evaluate, maxEq, valid], rel⟩

/-- Raise case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracRaise {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp) (env : List Value) (s : State C F)
    (bodyIH : EvalAt cc f [body] env s) : EvalAt cc f [.raise trace body] env s := by
  intro result next t ⟨run, noType, rel⟩
  rw [evaluate] at run ⊢
  cases bodyRun : evaluate [body] env s with
  | mk bodyResult middle =>
    rw [bodyRun] at run
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨target, targetRun, targetRel⟩ := bodyIH bodyResult middle t ⟨bodyRun, bodySafe, rel⟩
    rw [targetRun]
    cases bodyResult <;> cases run <;> exact ⟨target, rfl, targetRel⟩

/-- Tick case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracTick {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp) (env : List Value) (s : State C F)
    (bodyIH : s.clock ≠ 0 → EvalAt cc f [body] env (decClock 1 s)) :
    EvalAt cc f [.tick trace body] env s := by
  intro result next t ⟨run, noType, rel⟩
  have clockEq : t.clock = s.clock := by rcases rel with ⟨_, rfl⟩; rfl
  by_cases zero : s.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨t, by simp [evaluate, clockEq, zero], rel⟩
  · have reduced : adjOracRel cc f (decClock 1 s) (decClock 1 t) := by
      rcases rel with ⟨compatible, rfl⟩
      exact ⟨compatible, rfl⟩
    have bodyRun : evaluate [body] env (decClock 1 s) = (result, next) := by
      simpa [evaluate, zero] using run
    obtain ⟨target, targetRun, targetRel⟩ := bodyIH zero result next (decClock 1 t)
      ⟨bodyRun, noType, reduced⟩
    exact ⟨target, by simpa [evaluate, clockEq, zero] using targetRun, targetRel⟩

/-- Nonempty list case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracCons {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (first second : ClosLang.Exp) (rest : List ClosLang.Exp) (env : List Value) (s : State C F)
    (firstIH : EvalAt cc f [first] env s)
    (restIH : ∀ values middle, evaluate [first] env s = (.val values, middle) →
      EvalAt cc f (second :: rest) env middle) :
    EvalAt cc f (first :: second :: rest) env s := by
  intro result next t ⟨run, noType, rel⟩
  cases firstRun : evaluate [first] env s with
  | mk firstResult middle =>
    cases firstResult with
    | err error =>
      rw [evaluate_cons_error first (second :: rest) env s middle error firstRun] at run
      have safe : (Flapjack.SemanticPrimitivesHOL.Result.err error :
          Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
        cases run
        exact noType
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := firstIH (.err error) middle t ⟨firstRun, safe, rel⟩
      cases run
      exact ⟨targetMiddle, evaluate_cons_error first (second :: rest) env t targetMiddle error targetRun, middleRel⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value first env s middle values firstRun
      obtain ⟨targetMiddle, targetRun, middleRel⟩ :=
        firstIH (.val [value]) middle t ⟨firstRun, by simp, rel⟩
      rw [evaluate_cons_value first (second :: rest) env s middle value firstRun] at run
      rw [evaluate_cons_value first (second :: rest) env t targetMiddle value targetRun]
      cases restRun : evaluate (second :: rest) env middle with
      | mk restResult last =>
        rw [restRun] at run
        have restSafe : restResult ≠ .err (.abort .typeError) := by
          intro bad
          rw [bad] at run
          cases run
          exact noType rfl
        obtain ⟨targetLast, targetRest, lastRel⟩ :=
          restIH [value] middle firstRun restResult last targetMiddle ⟨restRun, restSafe, middleRel⟩
        rw [targetRest]
        cases restResult <;> cases run <;> exact ⟨targetLast, rfl, lastRel⟩

/-- Let-binding case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracLet {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (env : List Value) (s : State C F) (bindingsIH : EvalAt cc f bindings env s)
    (bodyIH : ∀ values middle, evaluate bindings env s = (.val values, middle) →
      EvalAt cc f [body] (values ++ env) middle) :
    EvalAt cc f [.let trace bindings body] env s := by
  intro result next t ⟨run, noType, rel⟩
  cases bindingsRun : evaluate bindings env s with
  | mk bindingsResult middle =>
    rw [evaluate, fixClock_evaluate, bindingsRun] at run
    have bindingsSafe : bindingsResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ :=
      bindingsIH bindingsResult middle t ⟨bindingsRun, bindingsSafe, rel⟩
    rw [evaluate, fixClock_evaluate, targetRun]
    cases bindingsResult with
    | err error => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
    | val values =>
      exact bodyIH values middle bindingsRun result next targetMiddle ⟨run, noType, middleRel⟩

/-- Exception-handler case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracHandle {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp) (env : List Value) (s : State C F)
    (bodyIH : EvalAt cc f [body] env s)
    (handlerIH : ∀ value middle, evaluate [body] env s = (.err (.raise value), middle) →
      EvalAt cc f [handler] (value :: env) middle) :
    EvalAt cc f [.handle trace body handler] env s := by
  intro result next t ⟨run, noType, rel⟩
  cases bodyRun : evaluate [body] env s with
  | mk bodyResult middle =>
    rw [evaluate, fixClock_evaluate, bodyRun] at run
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ := bodyIH bodyResult middle t ⟨bodyRun, bodySafe, rel⟩
    rw [evaluate, fixClock_evaluate, targetRun]
    cases bodyResult with
    | val values => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
    | err error =>
      cases error with
      | abort reason => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
      | raise value =>
        exact handlerIH value middle bodyRun result next targetMiddle ⟨run, noType, middleRel⟩

/-- Conditional case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracIf {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp) (env : List Value) (s : State C F)
    (conditionIH : EvalAt cc f [condition] env s)
    (yesIH : ∀ value middle, evaluate [condition] env s = (.val [value], middle) →
      asBool value = some true → EvalAt cc f [yes] env middle)
    (noIH : ∀ value middle, evaluate [condition] env s = (.val [value], middle) →
      asBool value = some false → EvalAt cc f [no] env middle) :
    EvalAt cc f [.ifThenElse trace condition yes no] env s := by
  intro result next t ⟨run, noType, rel⟩
  cases conditionRun : evaluate [condition] env s with
  | mk conditionResult middle =>
    rw [evaluate, fixClock_evaluate, conditionRun] at run
    have conditionSafe : conditionResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ :=
      conditionIH conditionResult middle t ⟨conditionRun, conditionSafe, rel⟩
    rw [evaluate, fixClock_evaluate, targetRun]
    cases conditionResult with
    | err error => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env s middle values conditionRun
      cases decision : asBool value with
      | none =>
        simp [decision] at run
        exact (noType run.1.symm).elim
      | some flag =>
        cases flag with
        | false =>
          have branchRun : evaluate [no] env middle = (result, next) := by
            simpa [Flapjack.holHd, decision] using run
          obtain ⟨target, targetBranch, targetRel⟩ :=
            noIH value middle conditionRun decision result next targetMiddle ⟨branchRun, noType, middleRel⟩
          exact ⟨target, by simpa [Flapjack.holHd, decision] using targetBranch, targetRel⟩
        | true =>
          have branchRun : evaluate [yes] env middle = (result, next) := by
            simpa [Flapjack.holHd, decision] using run
          obtain ⟨target, targetBranch, targetRel⟩ :=
            yesIH value middle conditionRun decision result next targetMiddle ⟨branchRun, noType, middleRel⟩
          exact ⟨target, by simpa [Flapjack.holHd, decision] using targetBranch, targetRel⟩

/-- Recursive-binding case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracLetrec {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (names : List Basis.Pure.MlString.MlString) (loc : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (env : List Value) (s : State C F)
    (bodyIH : ∀ captured, (functions.all (fun (arity, _) => arity ≤ s.maxApp && arity != 0) = true) →
      (match selected with | none => some env | some indices => lookupVars indices env) = some captured →
      EvalAt cc f [body]
        (((List.range functions.length).map (fun i => Value.recclosure loc [] captured functions i)) ++ env) s) :
    EvalAt cc f [.letrec names loc selected functions body] env s := by
  intro result next t ⟨run, noType, rel⟩
  have maxEq : t.maxApp = s.maxApp := by rcases rel with ⟨_, rfl⟩; rfl
  by_cases valid : functions.all (fun (arity, _) => arity ≤ s.maxApp && arity != 0) = true
  · cases selected with
    | none =>
      have sourceRun : evaluate [body]
          (((List.range functions.length).map (fun i => Value.recclosure loc [] env functions i)) ++ env) s =
          (result, next) := by simpa [evaluate, valid] using run
      obtain ⟨target, targetRun, targetRel⟩ := bodyIH env valid rfl result next t ⟨sourceRun, noType, rel⟩
      exact ⟨target, by simpa [evaluate, maxEq, valid] using targetRun, targetRel⟩
    | some indices =>
      cases captured : lookupVars indices env with
      | none =>
        simp [evaluate, valid, captured] at run
        exact (noType run.1.symm).elim
      | some values =>
        have sourceRun : evaluate [body]
            (((List.range functions.length).map (fun i => Value.recclosure loc [] values functions i)) ++ env) s =
            (result, next) := by simpa [evaluate, valid, captured] using run
        obtain ⟨target, targetRun, targetRel⟩ :=
          bodyIH values valid captured result next t ⟨sourceRun, noType, rel⟩
        exact ⟨target, by simpa [evaluate, maxEq, valid, captured] using targetRun, targetRel⟩
  · cases selected <;> simp [evaluate, valid] at run
    all_goals exact (noType run.1.symm).elim

/-- Direct-call case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracCall {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (ticks loc : Nat) (args : List ClosLang.Exp)
    (env : List Value) (s : State C F) (argsIH : EvalAt cc f args env s)
    (bodyIH : ∀ values middle callEnv body, evaluate args env s = (.val values, middle) →
      findCode loc values middle.code = some (callEnv, body) → ticks + 1 ≤ middle.clock →
      EvalAt cc f [body] callEnv (decClock (ticks + 1) middle)) :
    EvalAt cc f [.call trace ticks loc args] env s := by
  intro result next t ⟨run, noType, rel⟩
  cases argsRun : evaluate args env s with
  | mk argsResult middle =>
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH argsResult middle t ⟨argsRun, argsSafe, rel⟩
    rw [evaluate, fixClock_evaluate, targetRun]
    cases argsResult with
    | err error => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
    | val values =>
      have codeEq : targetMiddle.code = middle.code := by rcases middleRel with ⟨_, rfl⟩; rfl
      have clockEq : targetMiddle.clock = middle.clock := by rcases middleRel with ⟨_, rfl⟩; rfl
      cases codeRun : findCode loc values middle.code with
      | none =>
        simp [codeRun] at run
        exact (noType run.1.symm).elim
      | some pair =>
        rcases pair with ⟨callEnv, body⟩
        by_cases timeout : middle.clock < ticks + 1
        · simp [codeRun, timeout] at run
          obtain ⟨rfl, rfl⟩ := run
          have finalRel : adjOracRel cc f { middle with clock := 0 } { targetMiddle with clock := 0 } := by
            rcases middleRel with ⟨compatible, rfl⟩
            exact ⟨compatible, rfl⟩
          exact ⟨{ targetMiddle with clock := 0 }, by simp [codeEq, codeRun, clockEq, timeout], finalRel⟩
        · have reduced : adjOracRel cc f (decClock (ticks + 1) middle) (decClock (ticks + 1) targetMiddle) := by
            rcases middleRel with ⟨compatible, rfl⟩
            exact ⟨compatible, rfl⟩
          have bodyRun : evaluate [body] callEnv (decClock (ticks + 1) middle) = (result, next) := by
            simpa [codeRun, timeout] using run
          obtain ⟨target, targetBody, targetRel⟩ :=
            bodyIH values middle callEnv body argsRun codeRun (by omega) result next
              (decClock (ticks + 1) targetMiddle) ⟨bodyRun, noType, reduced⟩
          exact ⟨target, by simpa [codeEq, codeRun, clockEq, timeout] using targetBody, targetRel⟩

/-- Application expression case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracApp {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (location : Option Nat) (function : ClosLang.Exp)
    (args : List ClosLang.Exp) (env : List Value) (s : State C F)
    (argsIH : 0 < args.length → EvalAt cc f args env s)
    (functionIH : ∀ values middle, 0 < args.length → evaluate args env s = (.val values, middle) →
      EvalAt cc f [function] env middle)
    (appIH : ∀ values middle functions last, 0 < args.length → evaluate args env s = (.val values, middle) →
      evaluate [function] env middle = (.val functions, last) →
      AppAt cc f location (@Flapjack.holHd Value ⟨unitValue⟩ functions) values last) :
    EvalAt cc f [.app trace location function args] env s := by
  intro result next t ⟨run, noType, rel⟩
  cases args with
  | nil =>
    simp [evaluate] at run
    exact (noType run.1.symm).elim
  | cons first rest =>
    have nonempty : 0 < (first :: rest).length := by simp
    cases argsRun : evaluate (first :: rest) env s with
    | mk argsResult middle =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        rw [bad] at run
        cases run
        exact noType rfl
      obtain ⟨targetMiddle, targetRun, middleRel⟩ :=
        argsIH nonempty argsResult middle t ⟨argsRun, argsSafe, rel⟩
      rw [evaluate, fixClock_evaluate, targetRun]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run ⊢
      cases argsResult with
      | err error => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
      | val values =>
        cases functionRun : evaluate [function] env middle with
        | mk functionResult last =>
          rw [fixClock_evaluate, functionRun] at run
          have functionSafe : functionResult ≠ .err (.abort .typeError) := by
            intro bad
            rw [bad] at run
            cases run
            exact noType rfl
          obtain ⟨targetLast, targetFunction, lastRel⟩ :=
            functionIH values middle nonempty argsRun functionResult last targetMiddle
              ⟨functionRun, functionSafe, middleRel⟩
          rw [fixClock_evaluate, targetFunction]
          cases functionResult with
          | err error => cases run; exact ⟨targetLast, rfl, lastRel⟩
          | val functions =>
            exact appIH values middle functions last nonempty argsRun functionRun result next targetLast
              ⟨run, noType, lastRel⟩

/-- Empty-argument closure application case of the source mutual theorem. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppAdjOracNil {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (location : Option Nat) (function : Value) (s : State C F) : AppAt cc f location function [] s := by
  intro result next t ⟨run, _, rel⟩
  simp [evaluateApp] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨t, by simp [evaluateApp], rel⟩

/-- Nonempty closure-application case of the source mutual theorem. The
induction hypotheses follow the closure body and any remaining arguments. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppAdjOracCons {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (location : Option Nat) (function arg : Value) (args : List Value) (s : State C F)
    (bodyIH : ∀ body env rest,
      destClosure s.maxApp location function (arg :: args) = some (.fullApp body env rest) →
      (arg :: args).length - rest.length ≤ s.clock →
      EvalAt cc f [body] env (decClock ((arg :: args).length - rest.length) s))
    (appIH : ∀ body env rest value middle,
      destClosure s.maxApp location function (arg :: args) = some (.fullApp body env rest) →
      (arg :: args).length - rest.length ≤ s.clock →
      evaluate [body] env (decClock ((arg :: args).length - rest.length) s) = (.val [value], middle) →
      AppAt cc f location value rest middle) :
    AppAt cc f location function (arg :: args) s := by
  intro result next t ⟨run, noType, rel⟩
  have maxEq : t.maxApp = s.maxApp := by rcases rel with ⟨_, rfl⟩; rfl
  have clockEq : t.clock = s.clock := by rcases rel with ⟨_, rfl⟩; rfl
  cases closure : destClosure s.maxApp location function (arg :: args) with
  | none =>
    rw [evaluateApp, closure] at run
    dsimp only at run
    cases run
    exact (noType rfl).elim
  | some kind =>
    cases kind with
    | partialApp value =>
      by_cases timeout : s.clock < (arg :: args).length
      · rw [evaluateApp, closure] at run
        dsimp only at run
        rw [if_pos timeout] at run
        obtain ⟨rfl, rfl⟩ := run
        have nextRel : adjOracRel cc f { s with clock := 0 } { t with clock := 0 } := by
          rcases rel with ⟨compatible, rfl⟩
          exact ⟨compatible, rfl⟩
        refine ⟨{ t with clock := 0 }, ?_, nextRel⟩
        rw [evaluateApp, maxEq, closure]
        dsimp only
        rw [clockEq, if_pos timeout]
        rfl
      · rw [evaluateApp, closure] at run
        dsimp only at run
        rw [if_neg timeout] at run
        obtain ⟨rfl, rfl⟩ := run
        have nextRel : adjOracRel cc f (decClock (arg :: args).length s) (decClock (arg :: args).length t) := by
          rcases rel with ⟨compatible, rfl⟩
          exact ⟨compatible, rfl⟩
        refine ⟨decClock (arg :: args).length t, ?_, nextRel⟩
        rw [evaluateApp, maxEq, closure]
        dsimp only
        rw [clockEq, if_neg timeout]
    | fullApp body env rest =>
      by_cases timeout : s.clock < (arg :: args).length - rest.length
      · rw [evaluateApp, closure] at run
        dsimp only at run
        rw [if_pos timeout] at run
        obtain ⟨rfl, rfl⟩ := run
        have nextRel : adjOracRel cc f { s with clock := 0 } { t with clock := 0 } := by
          rcases rel with ⟨compatible, rfl⟩
          exact ⟨compatible, rfl⟩
        refine ⟨{ t with clock := 0 }, ?_, nextRel⟩
        rw [evaluateApp, maxEq, closure]
        dsimp only
        rw [clockEq, if_pos timeout]
        rfl
      · have reduced : adjOracRel cc f (decClock ((arg :: args).length - rest.length) s)
            (decClock ((arg :: args).length - rest.length) t) := by
          rcases rel with ⟨compatible, rfl⟩
          exact ⟨compatible, rfl⟩
        have enough : (arg :: args).length - rest.length ≤ s.clock := by omega
        rw [evaluateApp, closure] at run
        dsimp only at run
        rw [if_neg timeout, fixClock_evaluate] at run
        rw [evaluateApp, maxEq, closure]
        dsimp only
        rw [clockEq, if_neg timeout, fixClock_evaluate]
        cases bodyRun : evaluate [body] env (decClock ((arg :: args).length - rest.length) s) with
        | mk bodyResult middle =>
          rw [bodyRun] at run
          have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
            intro bad
            rw [bad] at run
            cases run
            exact noType rfl
          obtain ⟨targetMiddle, targetRun, middleRel⟩ :=
            bodyIH body env rest closure enough bodyResult middle _ ⟨bodyRun, bodySafe, reduced⟩
          rw [targetRun]
          cases bodyResult with
          | err error => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
          | val values =>
            cases values with
            | nil => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
            | cons value tail =>
              cases tail with
              | cons second tail => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
              | nil =>
                exact appIH body env rest value middle closure enough bodyRun result next targetMiddle
                  ⟨run, noType, middleRel⟩

/-- Thunk-forcing operation case of the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracForce {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (env : List Value) (s : State C F)
    (argsIH : EvalAt cc f args env s)
    (forceIH : ∀ values middle value, evaluate args env s = (.val values, middle) →
      destThunk values middle.refs = .isThunk .notEvaluated value →
      EvalAt cc f [appUnit (.var .none 0)] [value] middle) :
    EvalAt cc f [.op trace (.thunkOp .forceThunk) args] env s := by
  intro result next t ⟨run, noType, rel⟩
  cases argsRun : evaluate args env s with
  | mk argsResult middle =>
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH argsResult middle t ⟨argsRun, argsSafe, rel⟩
    rw [evaluate, fixClock_evaluate, targetRun]
    cases argsResult with
    | err error => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
    | val values =>
      have refsEq : targetMiddle.refs = middle.refs := by rcases middleRel with ⟨_, rfl⟩; rfl
      dsimp only at run ⊢
      cases thunkRun : destThunk values middle.refs with
      | badRef =>
        rw [thunkRun] at run
        cases run
        exact (noType rfl).elim
      | notThunk =>
        rw [thunkRun] at run
        cases run
        exact (noType rfl).elim
      | isThunk mode value =>
        rw [thunkRun] at run
        rw [refsEq, thunkRun]
        cases mode with
        | evaluated => cases run; exact ⟨targetMiddle, rfl, middleRel⟩
        | notEvaluated =>
          dsimp only at run ⊢
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
          | mk forceResult last =>
            rw [forceRun] at run
            have forceSafe : forceResult ≠ .err (.abort .typeError) := by
              intro bad
              rw [bad] at run
              cases run
              exact noType rfl
            obtain ⟨targetLast, targetForce, lastRel⟩ :=
              forceIH values middle value argsRun thunkRun forceResult last targetMiddle
                ⟨forceRun, forceSafe, middleRel⟩
            rw [targetForce]
            cases forceResult with
            | err error => cases run; exact ⟨targetLast, rfl, lastRel⟩
            | val forced =>
              have lastRefs : targetLast.refs = last.refs := by rcases lastRel with ⟨_, rfl⟩; rfl
              cases updateRun : updateThunk values last.refs forced with
              | none =>
                simp [updateRun] at run
                exact (noType run.1.symm).elim
              | some refs =>
                simp [updateRun] at run
                obtain ⟨rfl, rfl⟩ := run
                have updatedRel : adjOracRel cc f { last with refs := refs } { targetLast with refs := refs } := by
                  rcases lastRel with ⟨compatible, rfl⟩
                  exact ⟨compatible, rfl⟩
                exact ⟨{ targetLast with refs := refs }, by simp [lastRefs, updateRun], updatedRel⟩

/-- Ordinary-operation case of the source oracle-adjustment evaluator
simulation, with the induction hypothesis for its argument expressions. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracOrdinaryOp {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp)
    (env : List Value) (s : State C F) (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) (argsIH : EvalAt cc f args env s) :
    EvalAt cc f [.op trace op args] env s := by
  intro result next t ⟨run, noType, rel⟩
  rw [evaluate_ordinaryOp_eq trace op args env s notInstall notForce] at run
  rw [evaluate_ordinaryOp_eq trace op args env t notInstall notForce]
  cases argsRun : evaluate args env s with
  | mk argResult middle =>
    rw [argsRun] at run
    have argsSafe : argResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH argResult middle t ⟨argsRun, argsSafe, rel⟩
    rw [targetRun]
    cases argResult with
    | err error =>
      cases run
      exact ⟨targetMiddle, rfl, middleRel⟩
    | val values =>
      cases appRun : doApp op values.reverse middle with
      | err error =>
        simp only [appRun] at run
        have targetApp := doAppAdjOracErr cc f op values.reverse middle targetMiddle error ⟨appRun, middleRel⟩
        cases run
        exact ⟨targetMiddle, by simp [targetApp], middleRel⟩
      | val pair =>
        rcases pair with ⟨value, final⟩
        simp only [appRun] at run
        obtain ⟨targetFinal, targetApp, finalRel⟩ :=
          doAppAdjOracVal cc f op values.reverse middle targetMiddle value final ⟨appRun, middleRel⟩
        cases run
        exact ⟨targetFinal, by simp [targetApp], finalRel⟩

/-- Installation case of the source evaluator simulation. The second
induction hypothesis applies to the dynamically installed program. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOracInstall {C D F U : Type} (_unused : U) (cc : Compiler D) (f : C → D)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (env : List Value) (s : State C F)
    (argsIH : EvalAt cc f args env s)
    (installedIH : ∀ values middle program installed,
      evaluate args env s = (.val values, middle) →
      doInstall values.reverse middle = (.val program, installed) → EvalAt cc f program [] installed) :
    EvalAt cc f [.op trace .install args] env s := by
  intro result next t ⟨run, noType, rel⟩
  rw [evaluate_install_eq trace args env s] at run
  rw [evaluate_install_eq trace args env t]
  cases argsRun : evaluate args env s with
  | mk argResult middle =>
    rw [argsRun] at run
    have argsSafe : argResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH argResult middle t ⟨argsRun, argsSafe, rel⟩
    rw [targetRun]
    cases argResult with
    | err error =>
      cases run
      exact ⟨targetMiddle, rfl, middleRel⟩
    | val values =>
      unfold runInstalled at run ⊢
      dsimp only at run ⊢
      cases installRun : doInstall values.reverse middle with
      | mk installResult installed =>
        rw [installRun] at run
        cases installResult with
        | err error =>
          dsimp only at run
          have installSafe : (Flapjack.SemanticPrimitivesHOL.Result.err error :
              Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value) ≠ .err (.abort .typeError) := by
            intro bad
            have errorEq : error = .abort .typeError := by cases bad; rfl
            cases run
            exact noType (by rw [errorEq])
          obtain ⟨targetInstalled, targetInstall, installedRel⟩ :=
            doInstallAdjOrac cc f values.reverse middle (.err error) installed targetMiddle
              ⟨installRun, middleRel, installSafe⟩
          rw [targetInstall]
          cases run
          exact ⟨targetInstalled, rfl, installedRel⟩
        | val program =>
          dsimp only at run
          obtain ⟨targetInstalled, targetInstall, installedRel⟩ :=
            doInstallAdjOrac cc f values.reverse middle (.val program) installed targetMiddle
              ⟨installRun, middleRel, by simp⟩
          rw [targetInstall]
          dsimp only
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            rw [programRun] at run
            have programSafe : programResult ≠ .err (.abort .typeError) := by
              intro bad
              rw [bad] at run
              cases run
              exact noType rfl
            obtain ⟨targetFinal, targetProgram, finalRel⟩ :=
              installedIH values middle program installed argsRun installRun programResult final targetInstalled
                ⟨programRun, programSafe, installedRel⟩
            rw [targetProgram]
            cases programResult <;> cases run <;> exact ⟨targetFinal, rfl, finalRel⟩

end Flapjack.Compiler.Backend.ClosProps.AdjustOracle
