import Flapjack.Compiler.Backend.FlatPattern.Proofs.CompiledMatch
import Flapjack.Compiler.Backend.FlatPattern.Proofs.MatchRows

/-! Selected-row simulation for flat pattern compilation. The evaluator and
proof-side state/value relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A selected row's pattern matches with exactly the returned bindings. -/
theorem pmatchRows_selected_match {C F E : Type} (state : FlatSem.State C F) (value : FlatSem.Value)
    (rows : List (FlatLang.Pat × E)) (bindings : List (VarN × FlatSem.Value))
    (pattern : FlatLang.Pat) (body : E)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body)) :
    FlatSem.pmatch state pattern value [] = .match bindings := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows] at selected
  | cons row rows ih =>
    obtain ⟨first, expression⟩ := row
    cases head : FlatSem.pmatch state first value [] with
    | typeError => simp [FlatSem.pmatchRows, head] at selected
    | noMatch =>
      have tail : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body) := by
        simpa [FlatSem.pmatchRows, head] using selected
      exact ih tail
    | «match» newBindings =>
      cases tail : FlatSem.pmatchRows rows state value <;>
        simp_all [FlatSem.pmatchRows]

/-- If a source row matches, compiled pattern dispatch evaluates its compiled
body under an environment related to the source's bound-variable environment.
This is a proof-side composition, not yet a reviewed HOL theorem port. -/
theorem evaluate_compiled_match_branch {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (n m : Nat) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (source target final : FlatSem.State C F) (value value' : FlatSem.Value)
    (sourceEnv targetEnv dispatchEnv : FlatSem.Environment FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body default : FlatLang.Exp)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (envs : EnvRel m sourceEnv targetEnv) (nameBound : n ≤ m)
    (rowBound : (compileMatch cfg rows).1 < n - 1)
    (dispatchEq : dispatchEnv.v = (encNumToName n, value') :: targetEnv.v)
    (sourceMatch : FlatSem.pmatchRows rows source value = .match (bindings, pattern, body))
    (evaluated : FlatSem.evaluate dispatchEnv target
      [compilePats cfg (compileMatch cfg rows).2.1 trace n
        (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2] = (final, result)) :
    ∃ extEnv, FlatSem.evaluate extEnv target [(compileExp cfg body).2.2] = (final, result) ∧
      EnvRel (n - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv := by
  obtain ⟨index, targetBindings, bodyBound, flag, compiledBody, sourceAt, compiled, targetAt,
    bodyLe, patternLe, bindingRel, targetMatch⟩ :=
      compileMatch_pmatchRows_index_bound cfg stateCfg m source target value value' states values rows
        bindings pattern body sourceMatch
  have found : dispatchEnv.v.lookup (encNumToName n) = some value' := by simp [dispatchEq]
  have pure : FlatSem.evaluate dispatchEnv target [.varLocal trace (encNumToName n)] =
      (target, .val [value']) := by simp [FlatSem.evaluate, found]
  have targetSafe : FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' ≠ .typeError := by
    rw [targetMatch]; simp
  have dispatch := evaluate_compilePats cfg (compileMatch cfg rows).2.1 trace n
    (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2
    dispatchEnv target value' pure targetSafe
  have branchEval : FlatSem.evaluate dispatchEnv target
      [compilePatRhs trace n (.varLocal trace (encNumToName n)) (pattern, compiledBody)] = (final, result) := by
    rw [targetMatch] at dispatch
    exact dispatch.symm.trans evaluated
  have patternMatch := pmatchRows_selected_match target value' (compileMatch cfg rows).2.2
    targetBindings pattern compiledBody targetMatch
  have patternBound : maxDecName (FlatLang.patBindings pattern) < n - 1 := by omega
  obtain ⟨extEnv, extEval, extRelated⟩ := evaluate_compilePatRhs trace n m pattern compiledBody
    target final dispatchEnv sourceEnv targetEnv value' bindings targetBindings result branchEval patternMatch
    envs bindingRel dispatchEq nameBound patternBound
  exact ⟨extEnv, by simpa [compiled] using extEval, extRelated⟩

/-- When the source rows do not match, compiled dispatch evaluates the
provided default expression in the target environment. -/
theorem evaluate_compiled_match_default {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (n m : Nat) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (source target : FlatSem.State C F) (value value' : FlatSem.Value)
    (targetEnv dispatchEnv : FlatSem.Environment FlatSem.Value) (default : FlatLang.Exp)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (dispatchEq : dispatchEnv.v = (encNumToName n, value') :: targetEnv.v)
    (sourceMatch : FlatSem.pmatchRows rows source value = .noMatch) :
    FlatSem.evaluate dispatchEnv target
      [compilePats cfg (compileMatch cfg rows).2.1 trace n
        (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2] =
      FlatSem.evaluate dispatchEnv target [default] := by
  have related := compileMatch_pmatchRows_related cfg stateCfg m source target value value' states values rows
  have targetMatch : FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' = .noMatch := by
    simpa [sourceMatch] using related
  have found : dispatchEnv.v.lookup (encNumToName n) = some value' := by simp [dispatchEq]
  have pure : FlatSem.evaluate dispatchEnv target [.varLocal trace (encNumToName n)] =
      (target, .val [value']) := by simp [FlatSem.evaluate, found]
  have targetSafe : FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' ≠ .typeError := by
    rw [targetMatch]; simp
  have dispatch := evaluate_compilePats cfg (compileMatch cfg rows).2.1 trace n
    (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2
    dispatchEnv target value' pure targetSafe
  simpa [targetMatch] using dispatch

/-- Related flat errors either raise related values or carry the same abort. -/
inductive FlatErrorRel : SemanticPrimitivesHOL.ErrorResult FlatSem.Value →
    SemanticPrimitivesHOL.ErrorResult FlatSem.Value → Prop where
  | raise {left right} : ValueRel left right → FlatErrorRel (.raise left) (.raise right)
  | abort (reason : SemanticPrimitivesHOL.Abort) : FlatErrorRel (.abort reason) (.abort reason)

/-- Proof-side result relation for lists of values and errors. -/
inductive FlatResultRel : Result (List FlatSem.Value) FlatSem.Value →
    Result (List FlatSem.Value) FlatSem.Value → Prop where
  | values {left right} : List.Forall₂ ValueRel left right → FlatResultRel (.val left) (.val right)
  | error {left right} : FlatErrorRel left right → FlatResultRel (.err left) (.err right)

/-- A selected compiled row simulates its source body using the body's
induction hypothesis. The target execution is constructed by evaluation. -/
theorem compiled_match_branch_forward {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (n m : Nat) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (source target sourceFinal : FlatSem.State C F) (value value' : FlatSem.Value)
    (sourceEnv targetEnv dispatchEnv : FlatSem.Environment FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body default : FlatLang.Exp)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (envs : EnvRel m sourceEnv targetEnv) (nameBound : n ≤ m)
    (rowBound : (compileMatch cfg rows).1 < n - 1)
    (dispatchEq : dispatchEnv.v = (encNumToName n, value') :: targetEnv.v)
    (sourceMatch : FlatSem.pmatchRows rows source value = .match (bindings, pattern, body))
    (sourceBodyEval : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } source [body] =
      (sourceFinal, sourceResult))
    (bodyIH : ∀ extEnv, EnvRel (n - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
      FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } source [body] = (sourceFinal, sourceResult) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate extEnv target [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
        StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult) :
    ∃ targetFinal targetResult,
      FlatSem.evaluate dispatchEnv target
        [compilePats cfg (compileMatch cfg rows).2.1 trace n
          (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2] = (targetFinal, targetResult) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  cases targetRun : FlatSem.evaluate dispatchEnv target
      [compilePats cfg (compileMatch cfg rows).2.1 trace n
        (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2] with
  | mk targetFinal targetResult =>
    obtain ⟨extEnv, extEval, extRelated⟩ := evaluate_compiled_match_branch cfg stateCfg trace n m rows
      source target targetFinal value value' sourceEnv targetEnv dispatchEnv bindings pattern body default targetResult
      states values envs nameBound rowBound dispatchEq sourceMatch targetRun
    obtain ⟨final', result', bodyRun, finalRelated, resultRelated⟩ := bodyIH extEnv extRelated sourceBodyEval
    have equal : (targetFinal, targetResult) = (final', result') := extEval.symm.trans bodyRun
    cases equal
    exact ⟨_, _, rfl, finalRelated, resultRelated⟩

/-- Evaluating a successful singleton let-bound expression installs its value
before executing the let body, with the evaluator's clock adjustment. -/
theorem evaluate_let_singleton {C F : Type} (trace : BackendCommon.Tra) (name : VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (firstEval : FlatSem.evaluate env state [first] = (next, .val [value])) :
    FlatSem.evaluate env state [.let_ trace (some name) first body] =
      FlatSem.evaluate { env with v := (name, value) :: env.v }
        { next with clock := min state.clock next.clock } [body] := by
  simp [FlatSem.evaluate, firstEval, FlatSem.fixClock]

/-- A successful source match evaluates the selected body under its bindings. -/
theorem evaluate_mat_selected {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat)
    (body : FlatLang.Exp)
    (scrutineeEval : FlatSem.evaluate env state [scrutinee] = (next, .val [value]))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value =
      .match (bindings, pattern, body)) (distinct : (FlatLang.patBindings pattern).Nodup) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      FlatSem.evaluate { env with v := bindings ++ env.v } { next with clock := min state.clock next.clock } [body] := by
  simp only [FlatSem.evaluate, scrutineeEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- An unmatched source match raises the standard binding exception. -/
theorem evaluate_mat_noMatch {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (scrutineeEval : FlatSem.evaluate env state [scrutinee] = (next, .val [value]))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value = .noMatch) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err (.raise FlatSem.bindExnV)) := by
  simp only [FlatSem.evaluate, scrutineeEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- The match-expression compilation exposes the generated binding and
pattern-dispatch body. -/
theorem compileExp_mat_body (cfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileExp cfg (.mat trace scrutinee rows)).2.2 =
      .let_ trace (some (encNumToName (max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2)))
        (compileExp cfg scrutinee).2.2
        (compilePats cfg (compileMatch cfg rows).2.1 trace
          (max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2)
          (.varLocal trace (encNumToName (max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2)))
          (.raise trace (.con trace (some (0, none)) [])) (compileMatch cfg rows).2.2) := by
  cases first : compileExp cfg scrutinee with
  | mk bound rest =>
    cases rest with
    | mk flag expression =>
      cases matchResult : compileMatch cfg rows with
      | mk rowBound rest =>
        cases rest with
        | mk rowFlag compiledRows => simp [compileExp, first, matchResult]

/-- Selected match-expression case after the scrutinee simulation has
produced related values and post-states. The remaining premise is the
induction hypothesis for the selected source body. -/
theorem compile_mat_selected_forward {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (sourceStart sourceNext targetStart targetNext sourceFinal : FlatSem.State C F)
    (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (value value' : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (m : Nat)
    (sourceScrutinee : FlatSem.evaluate sourceEnv sourceStart [scrutinee] = (sourceNext, .val [value]))
    (targetScrutinee : FlatSem.evaluate targetEnv targetStart [(compileExp cfg scrutinee).2.2] =
      (targetNext, .val [value']))
    (states : StateRel stateCfg { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock })
    (values : ValueRel value value') (envs : EnvRel m sourceEnv targetEnv)
    (bound : max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2 ≤ m)
    (selected : FlatSem.pmatchRows rows { sourceNext with clock := min sourceStart.clock sourceNext.clock } value =
      .match (bindings, pattern, body)) (distinct : (FlatLang.patBindings pattern).Nodup)
    (sourceBodyEval : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v }
      { sourceNext with clock := min sourceStart.clock sourceNext.clock } [body] = (sourceFinal, sourceResult))
    (bodyIH : ∀ extEnv,
      EnvRel (max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2 - 1)
        { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
      FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v }
        { sourceNext with clock := min sourceStart.clock sourceNext.clock } [body] = (sourceFinal, sourceResult) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate extEnv { targetNext with clock := min targetStart.clock targetNext.clock }
          [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
        StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult) :
    FlatSem.evaluate sourceEnv sourceStart [.mat trace scrutinee rows] = (sourceFinal, sourceResult) ∧
    ∃ targetFinal targetResult,
      FlatSem.evaluate targetEnv targetStart [(compileExp cfg (.mat trace scrutinee rows)).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  let n := max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2
  let dispatchEnv := { targetEnv with v := (encNumToName n, value') :: targetEnv.v }
  have sourceRun := evaluate_mat_selected trace scrutinee rows sourceEnv sourceStart sourceNext value
    bindings pattern body sourceScrutinee selected distinct
  have rowBound : (compileMatch cfg rows).1 < n - 1 := by dsimp [n]; omega
  obtain ⟨targetFinal, targetResult, dispatchRun, finalRel, resultRel⟩ :=
    compiled_match_branch_forward cfg stateCfg trace n m rows
      { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock } sourceFinal value value'
      sourceEnv targetEnv dispatchEnv bindings pattern body (.raise trace (.con trace (some (0, none)) []))
      sourceResult states values envs bound rowBound rfl selected sourceBodyEval bodyIH
  constructor
  · exact sourceRun.trans sourceBodyEval
  · refine ⟨targetFinal, targetResult, ?_, finalRel, resultRel⟩
    rw [compileExp_mat_body]
    rw [evaluate_let_singleton trace (encNumToName n) (compileExp cfg scrutinee).2.2 _
      targetEnv targetStart targetNext value' targetScrutinee]
    exact dispatchRun

/-- The generated default expression raises the flat binding exception. -/
theorem evaluate_generated_bind_failure {C F : Type} (trace : BackendCommon.Tra)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [.raise trace (.con trace (some (0, none)) [])] =
      (state, .err (.raise FlatSem.bindExnV)) := by
  simp [FlatSem.evaluate, FlatSem.bindExnV, BackendCommon.bindTag]

/-- The unmatched match-expression case raises the same exception on both
sides after related scrutinees have been evaluated. -/
theorem compile_mat_noMatch_forward {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (sourceStart sourceNext targetStart targetNext : FlatSem.State C F)
    (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (value value' : FlatSem.Value)
    (sourceScrutinee : FlatSem.evaluate sourceEnv sourceStart [scrutinee] = (sourceNext, .val [value]))
    (targetScrutinee : FlatSem.evaluate targetEnv targetStart [(compileExp cfg scrutinee).2.2] =
      (targetNext, .val [value']))
    (states : StateRel stateCfg { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock })
    (values : ValueRel value value')
    (selected : FlatSem.pmatchRows rows { sourceNext with clock := min sourceStart.clock sourceNext.clock } value = .noMatch) :
    ∃ sourceFinal targetFinal sourceResult targetResult,
      FlatSem.evaluate sourceEnv sourceStart [.mat trace scrutinee rows] = (sourceFinal, sourceResult) ∧
      FlatSem.evaluate targetEnv targetStart [(compileExp cfg (.mat trace scrutinee rows)).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  let n := max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2
  let dispatchEnv := { targetEnv with v := (encNumToName n, value') :: targetEnv.v }
  have sourceRun := evaluate_mat_noMatch trace scrutinee rows sourceEnv sourceStart sourceNext value sourceScrutinee selected
  have dispatch := evaluate_compiled_match_default cfg stateCfg trace n n rows
    { sourceNext with clock := min sourceStart.clock sourceNext.clock }
    { targetNext with clock := min targetStart.clock targetNext.clock } value value' targetEnv dispatchEnv
    (.raise trace (.con trace (some (0, none)) [])) states values rfl selected
  have resultRel : FlatResultRel (.err (.raise FlatSem.bindExnV)) (.err (.raise FlatSem.bindExnV)) := by
    apply FlatResultRel.error
    apply FlatErrorRel.raise
    apply (valueRel_conv (some (BackendCommon.bindTag, none)) [] _).2
    exact ⟨[], rfl, .nil⟩
  refine ⟨_, _, _, _, sourceRun, ?_, states, resultRel⟩
  rw [compileExp_mat_body]
  rw [evaluate_let_singleton trace (encNumToName n) (compileExp cfg scrutinee).2.2 _
    targetEnv targetStart targetNext value' targetScrutinee]
  rw [dispatch]
  exact evaluate_generated_bind_failure trace dispatchEnv _

end Flapjack.Compiler.Backend.FlatPattern
