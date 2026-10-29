import Flapjack.Compiler.Backend.FlatPattern.Proofs.MatchBranch

/-! Exception-handler cases of the flat pattern compiler simulation. The
proof-side evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A raised exception enters the matching handler row with its bindings. -/
theorem evaluate_handle_selected {C F : Type} (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat)
    (body : FlatLang.Exp)
    (protectedExprEval : FlatSem.evaluate env state [protectedExpr] = (next, .err (.raise value)))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value =
      .match (bindings, pattern, body)) (distinct : (FlatLang.patBindings pattern).Nodup) :
    FlatSem.evaluate env state [.handle trace protectedExpr rows] =
      FlatSem.evaluate { env with v := bindings ++ env.v } { next with clock := min state.clock next.clock } [body] := by
  simp only [FlatSem.evaluate, protectedExprEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- A handler with no matching row propagates its raised exception. -/
theorem evaluate_handle_noMatch {C F : Type} (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (protectedExprEval : FlatSem.evaluate env state [protectedExpr] = (next, .err (.raise value)))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value = .noMatch) :
    FlatSem.evaluate env state [.handle trace protectedExpr rows] =
      ({ next with clock := min state.clock next.clock }, .err (.raise value)) := by
  simp only [FlatSem.evaluate, protectedExprEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- The compiler's generated handler binds the raised value under its fresh name. -/
theorem evaluate_handle_generated {C F : Type} (trace : BackendCommon.Tra) (name : VarN)
    (protectedExpr dispatch : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (protectedExprEval : FlatSem.evaluate env state [protectedExpr] = (next, .err (.raise value))) :
    FlatSem.evaluate env state [.handle trace protectedExpr [(.pvar name, dispatch)]] =
      FlatSem.evaluate { env with v := (name, value) :: env.v }
        { next with clock := min state.clock next.clock } [dispatch] := by
  simp only [FlatSem.evaluate, protectedExprEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow, FlatSem.pmatchRows, FlatSem.pmatch, FlatLang.patBindings]
  obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
  rfl

/-- Compilation replaces all handler rows with one fresh-variable handler. -/
theorem compileExp_handle_body (cfg : Config) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileExp cfg (.handle trace protectedExpr rows)).2.2 =
      .handle trace (compileExp cfg protectedExpr).2.2
        [(.pvar (encNumToName (max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2)),
          compilePats cfg (compileMatch cfg rows).2.1 trace
            (max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2)
            (.varLocal trace (encNumToName (max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2)))
            (.raise trace (.varLocal trace (encNumToName (max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2))))
            (compileMatch cfg rows).2.2)] := by
  cases first : compileExp cfg protectedExpr with
  | mk bound rest =>
    cases rest with
    | mk flag expression =>
      cases matchResult : compileMatch cfg rows with
      | mk rowBound rest =>
        cases rest with
        | mk rowFlag compiledRows => simp [compileExp, first, matchResult]

/-- The unmatched generated handler re-raises the bound exception. -/
theorem evaluate_generated_reraise {C F : Type} (trace : BackendCommon.Tra) (name : VarN)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (found : env.v.lookup name = some value) :
    FlatSem.evaluate env state [.raise trace (.varLocal trace name)] = (state, .err (.raise value)) := by
  simp [FlatSem.evaluate, found]

/-- Selected-handler case after the protected expression has raised related
values in related post-states. The remaining premise is the selected body's
induction hypothesis. -/
theorem compile_handle_selected_forward {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (sourceStart sourceNext targetStart targetNext sourceFinal : FlatSem.State C F)
    (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (value value' : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (m : Nat)
    (sourceProtected : FlatSem.evaluate sourceEnv sourceStart [protectedExpr] = (sourceNext, .err (.raise value)))
    (targetProtected : FlatSem.evaluate targetEnv targetStart [(compileExp cfg protectedExpr).2.2] =
      (targetNext, .err (.raise value')))
    (states : StateRel stateCfg { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock })
    (values : ValueRel value value') (envs : EnvRel m sourceEnv targetEnv)
    (bound : max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2 ≤ m)
    (selected : FlatSem.pmatchRows rows { sourceNext with clock := min sourceStart.clock sourceNext.clock } value =
      .match (bindings, pattern, body)) (distinct : (FlatLang.patBindings pattern).Nodup)
    (sourceBodyEval : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v }
      { sourceNext with clock := min sourceStart.clock sourceNext.clock } [body] = (sourceFinal, sourceResult))
    (bodyIH : ∀ extEnv,
      EnvRel (max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2 - 1)
        { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
      FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v }
        { sourceNext with clock := min sourceStart.clock sourceNext.clock } [body] = (sourceFinal, sourceResult) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate extEnv { targetNext with clock := min targetStart.clock targetNext.clock }
          [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
        StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult) :
    FlatSem.evaluate sourceEnv sourceStart [.handle trace protectedExpr rows] = (sourceFinal, sourceResult) ∧
    ∃ targetFinal targetResult,
      FlatSem.evaluate targetEnv targetStart [(compileExp cfg (.handle trace protectedExpr rows)).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  let n := max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2
  let dispatchEnv := { targetEnv with v := (encNumToName n, value') :: targetEnv.v }
  have sourceRun := evaluate_handle_selected trace protectedExpr rows sourceEnv sourceStart sourceNext value
    bindings pattern body sourceProtected selected distinct
  have rowBound : (compileMatch cfg rows).1 < n - 1 := by dsimp [n]; omega
  obtain ⟨targetFinal, targetResult, dispatchRun, finalRel, resultRel⟩ :=
    compiled_match_branch_forward cfg stateCfg trace n m rows
      { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock } sourceFinal value value'
      sourceEnv targetEnv dispatchEnv bindings pattern body (.raise trace (.varLocal trace (encNumToName n)))
      sourceResult states values envs bound rowBound rfl selected sourceBodyEval bodyIH
  constructor
  · exact sourceRun.trans sourceBodyEval
  · refine ⟨targetFinal, targetResult, ?_, finalRel, resultRel⟩
    rw [compileExp_handle_body]
    rw [evaluate_handle_generated trace (encNumToName n) (compileExp cfg protectedExpr).2.2 _
      targetEnv targetStart targetNext value' targetProtected]
    exact dispatchRun

/-- When no handler matches, compiled dispatch re-raises a related exception. -/
theorem compile_handle_noMatch_forward {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (sourceStart sourceNext targetStart targetNext : FlatSem.State C F)
    (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (value value' : FlatSem.Value)
    (sourceProtected : FlatSem.evaluate sourceEnv sourceStart [protectedExpr] = (sourceNext, .err (.raise value)))
    (targetProtected : FlatSem.evaluate targetEnv targetStart [(compileExp cfg protectedExpr).2.2] =
      (targetNext, .err (.raise value')))
    (states : StateRel stateCfg { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock })
    (values : ValueRel value value')
    (selected : FlatSem.pmatchRows rows { sourceNext with clock := min sourceStart.clock sourceNext.clock } value = .noMatch) :
    ∃ sourceFinal targetFinal sourceResult targetResult,
      FlatSem.evaluate sourceEnv sourceStart [.handle trace protectedExpr rows] = (sourceFinal, sourceResult) ∧
      FlatSem.evaluate targetEnv targetStart [(compileExp cfg (.handle trace protectedExpr rows)).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  let n := max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2
  let dispatchEnv := { targetEnv with v := (encNumToName n, value') :: targetEnv.v }
  have sourceRun := evaluate_handle_noMatch trace protectedExpr rows sourceEnv sourceStart sourceNext value sourceProtected selected
  have dispatch := evaluate_compiled_match_default cfg stateCfg trace n n rows
    { sourceNext with clock := min sourceStart.clock sourceNext.clock }
    { targetNext with clock := min targetStart.clock targetNext.clock } value value' targetEnv dispatchEnv
    (.raise trace (.varLocal trace (encNumToName n))) states values rfl selected
  have resultRel : FlatResultRel (.err (.raise value)) (.err (.raise value')) := .error (.raise values)
  refine ⟨_, _, _, _, sourceRun, ?_, states, resultRel⟩
  rw [compileExp_handle_body]
  rw [evaluate_handle_generated trace (encNumToName n) (compileExp cfg protectedExpr).2.2 _
    targetEnv targetStart targetNext value' targetProtected]
  rw [dispatch]
  apply evaluate_generated_reraise
  simp [dispatchEnv]

/-- A handler leaves normal results and aborts unchanged after clock fixing. -/
theorem evaluate_handle_passthrough {C F : Type} (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (protectedEval : FlatSem.evaluate env state [protectedExpr] = (next, result))
    (notRaised : ∀ value, result ≠ .err (.raise value)) :
    FlatSem.evaluate env state [.handle trace protectedExpr rows] =
      ({ next with clock := min state.clock next.clock }, result) := by
  cases result with
  | val values => simp [FlatSem.evaluate, protectedEval, FlatSem.fixClock]
  | err error =>
    cases error with
    | raise value => exact (notRaised value rfl).elim
    | abort reason => simp [FlatSem.evaluate, protectedEval, FlatSem.fixClock]

/-- Clock fixing preserves the proof-side state relation when both the input
and evaluated states are related. -/
theorem stateRel_fixClock {C F : Type} (cfg : Config)
    (sourceStart sourceNext targetStart targetNext : FlatSem.State C F)
    (starts : StateRel cfg sourceStart targetStart) (nexts : StateRel cfg sourceNext targetNext) :
    StateRel cfg { sourceNext with clock := min sourceStart.clock sourceNext.clock }
      { targetNext with clock := min targetStart.clock targetNext.clock } := by
  rcases starts with ⟨startClock, _, _, _, _⟩
  rcases nexts with ⟨nextClock, refs, ffi, globals, install⟩
  exact ⟨by simp [startClock, nextClock], refs, ffi, globals, install⟩

/-- Related results agree on whether an exception was raised. -/
theorem flatResultRel_notRaised (sourceResult targetResult : Result (List FlatSem.Value) FlatSem.Value)
    (related : FlatResultRel sourceResult targetResult)
    (notRaised : ∀ value, sourceResult ≠ .err (.raise value)) :
    ∀ value, targetResult ≠ .err (.raise value) := by
  cases related with
  | values related => simp
  | error related =>
    cases related with
    | raise related => exact (notRaised _ rfl).elim
    | abort reason => simp

/-- Normal results and aborts pass through compiled handlers with their
state and result relations preserved. -/
theorem compile_handle_passthrough {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (sourceStart sourceNext targetStart targetNext : FlatSem.State C F)
    (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value)
    (sourceResult targetResult : Result (List FlatSem.Value) FlatSem.Value)
    (sourceProtected : FlatSem.evaluate sourceEnv sourceStart [protectedExpr] = (sourceNext, sourceResult))
    (targetProtected : FlatSem.evaluate targetEnv targetStart [(compileExp cfg protectedExpr).2.2] =
      (targetNext, targetResult))
    (starts : StateRel stateCfg sourceStart targetStart) (nexts : StateRel stateCfg sourceNext targetNext)
    (related : FlatResultRel sourceResult targetResult)
    (notRaised : ∀ value, sourceResult ≠ .err (.raise value)) :
    ∃ sourceFinal targetFinal,
      FlatSem.evaluate sourceEnv sourceStart [.handle trace protectedExpr rows] = (sourceFinal, sourceResult) ∧
      FlatSem.evaluate targetEnv targetStart [(compileExp cfg (.handle trace protectedExpr rows)).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal := by
  refine ⟨_, _, evaluate_handle_passthrough trace protectedExpr rows sourceEnv sourceStart sourceNext
    sourceResult sourceProtected notRaised, ?_, stateRel_fixClock stateCfg sourceStart sourceNext targetStart targetNext starts nexts⟩
  rw [compileExp_handle_body]
  apply evaluate_handle_passthrough
  · exact targetProtected
  · exact flatResultRel_notRaised sourceResult targetResult related notRaised

/-- A handler whose row match type-fails returns a type error. -/
theorem evaluate_handle_rowTypeError {C F : Type} (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (protectedEval : FlatSem.evaluate env state [protectedExpr] = (next, .err (.raise value)))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value = .typeError) :
    FlatSem.evaluate env state [.handle trace protectedExpr rows] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, protectedEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- Duplicate names in the selected handler pattern cause a type error. -/
theorem evaluate_handle_duplicate {C F : Type} (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (protectedEval : FlatSem.evaluate env state [protectedExpr] = (next, .err (.raise value)))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value =
      .match (bindings, pattern, body)) (duplicate : ¬(FlatLang.patBindings pattern).Nodup) :
    FlatSem.evaluate env state [.handle trace protectedExpr rows] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, protectedEval, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- The name bound for a compiled handler is the maximum of its two parts plus two. -/
theorem compileExp_handle_bound (cfg : Config) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileExp cfg (.handle trace protectedExpr rows)).1 =
      max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2 := by
  cases first : compileExp cfg protectedExpr with
  | mk bound rest =>
    cases rest with
    | mk flag expression =>
      cases matchResult : compileMatch cfg rows with
      | mk rowBound rest =>
        cases rest with
        | mk rowFlag compiledRows => simp [compileExp, first, matchResult]

/-- The standard forward-simulation induction hypothesis for one expression.
This is Flapjack proof infrastructure over the unreviewed flat evaluator. -/
def ExpressionSimulation {C F : Type} (cfg stateCfg : Config) (expression : FlatLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
    FlatSem.evaluate sourceEnv source [expression] = (sourceFinal, sourceResult) →
    EnvRel n sourceEnv targetEnv → StateRel stateCfg source target → (compileExp cfg expression).1 < n →
    sourceResult ≠ .err (.abort .typeError) →
    ∃ targetFinal targetResult,
      FlatSem.evaluate targetEnv target [(compileExp cfg expression).2.2] = (targetFinal, targetResult) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult

/-- Handler expressions satisfy the forward simulation if their protected
expression and row bodies satisfy their induction hypotheses. -/
theorem compile_handle_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (protectedExpr : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (protectedIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg protectedExpr)
    (bodiesIH : ∀ pattern body, (pattern, body) ∈ rows → ExpressionSimulation (C := C) (F := F) cfg stateCfg body) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.handle trace protectedExpr rows) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  have generatedBound : max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2 < n := by
    simpa [compileExp_handle_bound] using bound
  have protectedBound : (compileExp cfg protectedExpr).1 < n := by omega
  cases protectedRun : FlatSem.evaluate sourceEnv source [protectedExpr] with
  | mk sourceNext protectedResult =>
    have protectedSafe : protectedResult ≠ .err (.abort .typeError) := by
      intro bad
      subst protectedResult
      have run := evaluate_handle_passthrough trace protectedExpr rows sourceEnv source sourceNext
        (.err (.abort .typeError)) protectedRun (by simp)
      rw [sourceEval] at run
      exact safe (congrArg Prod.snd run)
    obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := protectedIH
      sourceEnv targetEnv source target sourceNext protectedResult n protectedRun envs states protectedBound protectedSafe
    cases related with
    | values valuesRel =>
      obtain ⟨sourceFinal', targetFinal, sourceRun, targetRun', finalRel⟩ :=
        compile_handle_passthrough cfg stateCfg trace protectedExpr rows source sourceNext target targetNext
          sourceEnv targetEnv _ _ protectedRun targetRun states nextStates (.values valuesRel) (by simp)
      have equal := sourceEval.symm.trans sourceRun
      cases equal
      exact ⟨targetFinal, _, targetRun', finalRel, .values valuesRel⟩
    | error errorRel =>
      cases errorRel with
      | abort reason =>
        obtain ⟨sourceFinal', targetFinal, sourceRun, targetRun', finalRel⟩ :=
          compile_handle_passthrough cfg stateCfg trace protectedExpr rows source sourceNext target targetNext
            sourceEnv targetEnv _ _ protectedRun targetRun states nextStates (.error (.abort reason)) (by simp)
        have equal := sourceEval.symm.trans sourceRun
        cases equal
        exact ⟨targetFinal, _, targetRun', finalRel, .error (.abort reason)⟩
      | raise valuesRel =>
        rename_i value value'
        let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
        let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
        have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
          stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
        cases rowResult : FlatSem.pmatchRows rows sourceFixed value with
        | typeError =>
          have run := evaluate_handle_rowTypeError trace protectedExpr rows sourceEnv source sourceNext value
            protectedRun rowResult
          rw [sourceEval] at run
          exact (safe (congrArg Prod.snd run)).elim
        | noMatch =>
          obtain ⟨sourceFinal', targetFinal, sourceResult', targetResult', sourceRun, targetRun', finalRel, resultRel⟩ :=
            compile_handle_noMatch_forward cfg stateCfg trace protectedExpr rows source sourceNext target targetNext
              sourceEnv targetEnv value value' protectedRun targetRun fixedStates valuesRel rowResult
          have equal := sourceEval.symm.trans sourceRun
          cases equal
          exact ⟨targetFinal, targetResult', targetRun', finalRel, resultRel⟩
        | «match» selected =>
          rcases selected with ⟨bindings, pattern, body⟩
          have distinct : (FlatLang.patBindings pattern).Nodup := by
            by_cases distinct : (FlatLang.patBindings pattern).Nodup
            · exact distinct
            · have run := evaluate_handle_duplicate trace protectedExpr rows sourceEnv source sourceNext value
                bindings pattern body protectedRun rowResult distinct
              rw [sourceEval] at run
              exact (safe (congrArg Prod.snd run)).elim
          have sourceBody : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] =
              (sourceFinal, sourceResult) := by
            have run := evaluate_handle_selected trace protectedExpr rows sourceEnv source sourceNext value
              bindings pattern body protectedRun rowResult distinct
            exact run.symm.trans sourceEval
          have member := pmatchRows_match_mem sourceFixed value rows bindings pattern body rowResult
          have bodySim := bodiesIH pattern body member
          let generated := max (compileExp cfg protectedExpr).1 (compileMatch cfg rows).1 + 2
          have bodyBound : (compileExp cfg body).1 < generated - 1 := by
            have bodyLe := (compileMatch_member_bound cfg rows pattern body member).1
            dsimp [generated]
            omega
          have bodyIH : ∀ extEnv,
              EnvRel (generated - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
              FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] = (sourceFinal, sourceResult) →
              ∃ targetFinal targetResult,
                FlatSem.evaluate extEnv targetFixed [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
                StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
            intro extEnv envRel evaluated
            exact bodySim _ _ _ _ _ _ _ evaluated envRel fixedStates bodyBound safe
          obtain ⟨_, targetFinal, targetResult, targetRun', finalRel, resultRel⟩ :=
            compile_handle_selected_forward cfg stateCfg trace protectedExpr rows source sourceNext target targetNext sourceFinal
              sourceEnv targetEnv value value' bindings pattern body sourceResult n protectedRun targetRun fixedStates
              valuesRel envs (by dsimp [generated] at *; omega) rowResult distinct sourceBody bodyIH
          exact ⟨targetFinal, targetResult, targetRun', finalRel, resultRel⟩

end Flapjack.Compiler.Backend.FlatPattern
