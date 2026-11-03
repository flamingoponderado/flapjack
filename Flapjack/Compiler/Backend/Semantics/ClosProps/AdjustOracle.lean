import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal
import Flapjack.Compiler.Backend.BackendProps.StateCompiler
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

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

/-- Installation continuation factored out for the oracle-adjustment
simulation; this helper has no independent HOL declaration. -/
noncomputable def runInstalled {C F : Type} (values : List Value) (state : State C F) : EvalResult C F :=
  match doInstall values state with
  | (.err error, next) => (.err error, next)
  | (.val program, next) =>
    let (result, last) := evaluate program [] next
    match result with
    | .err error => (.err error, last)
    | .val values => (.val [@Flapjack.holLast Value ⟨unitValue⟩ values], last)

/-- Unfold the install operation at its argument evaluation boundary. -/
theorem evaluateInstallEq {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    evaluate [.op trace .install args] env state =
      match evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runInstalled values.reverse next := by
  rw [evaluate, fixClock_evaluate]
  cases evaluated : evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runInstalled
      split <;> simp_all
      split <;> simp_all
      rfl

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
  rw [evaluateInstallEq trace args env s] at run
  rw [evaluateInstallEq trace args env t]
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
