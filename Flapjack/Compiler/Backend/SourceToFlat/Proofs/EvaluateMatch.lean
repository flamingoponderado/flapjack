import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl

/-! Connecting source row selection to source evaluation. These Flapjack
helpers use the full clocked evaluator but are not HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- If source matching selects no row and does not type-error, evaluation
re-raises the designated fallback value. -/
theorem evaluateMatch_noMatch {F : Type} (st : State F) (env : SemEnv Value)
    (value errorValue : Value) (rows : List (Pat × AstHOL.Exp))
    (safe : ∀ next, EvaluateHOL.evaluateMatch st env value rows errorValue ≠
      (next, .err (.abort .typeError)))
    (selected : sourcePmatchRows env st value rows = .noMatch) :
    EvaluateHOL.evaluateMatch st env value rows errorValue = (st, .err (.raise errorValue)) := by
  induction rows with
  | nil => simp [EvaluateHOL.evaluateMatch]
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    by_cases unique : (patBindings pattern).Nodup
    · cases matching : pmatch env.c st.refs pattern value [] with
      | typeError => simp [sourcePmatchRows, matching] at selected
      | «match» bindings => simp [sourcePmatchRows, matching] at selected
      | noMatch =>
        have restSafe : ∀ next, EvaluateHOL.evaluateMatch st env value rest errorValue ≠
            (next, .err (.abort .typeError)) := by
          intro next bad
          apply safe next
          simpa [EvaluateHOL.evaluateMatch, unique, matching] using bad
        have restSelected : sourcePmatchRows env st value rest = .noMatch := by
          simpa [sourcePmatchRows, matching] using selected
        simpa [EvaluateHOL.evaluateMatch, unique, matching] using ih restSafe restSelected
    · have bad : EvaluateHOL.evaluateMatch st env value ((pattern, body) :: rest) errorValue =
          (st, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateMatch, unique, EvaluateHOL.typeError]
      exact (safe st bad).elim

/-- If source matching selects a row and does not type-error, its bindings
are distinct and evaluation runs the selected body in the extended namespace. -/
theorem evaluateMatch_selected {F : Type} (st : State F) (env : SemEnv Value)
    (value errorValue : Value) (rows : List (Pat × AstHOL.Exp))
    (bindings : List (VarN × Value)) (pattern : Pat) (body : AstHOL.Exp)
    (safe : ∀ next, EvaluateHOL.evaluateMatch st env value rows errorValue ≠
      (next, .err (.abort .typeError)))
    (selected : sourcePmatchRows env st value rows = .match (bindings, pattern, body)) :
    (patBindings pattern).Nodup ∧
      EvaluateHOL.evaluateMatch st env value rows errorValue =
        EvaluateHOL.evaluate st { env with v := nsAppend (alistToNs bindings) env.v } [body] := by
  induction rows with
  | nil => simp [sourcePmatchRows] at selected
  | cons row rest ih =>
    obtain ⟨headPattern, headBody⟩ := row
    by_cases unique : (patBindings headPattern).Nodup
    · cases matching : pmatch env.c st.refs headPattern value [] with
      | typeError => simp [sourcePmatchRows, matching] at selected
      | noMatch =>
        have restSafe : ∀ next, EvaluateHOL.evaluateMatch st env value rest errorValue ≠
            (next, .err (.abort .typeError)) := by
          intro next bad
          apply safe next
          simpa [EvaluateHOL.evaluateMatch, unique, matching] using bad
        have restSelected : sourcePmatchRows env st value rest = .match (bindings, pattern, body) := by
          simpa [sourcePmatchRows, matching] using selected
        obtain ⟨distinct, run⟩ := ih restSafe restSelected
        exact ⟨distinct, by simpa [EvaluateHOL.evaluateMatch, unique, matching] using run⟩
      | «match» bound =>
        simp only [sourcePmatchRows, matching, MatchResult.match.injEq, Prod.mk.injEq] at selected
        obtain ⟨rfl, rfl, rfl⟩ := selected
        exact ⟨unique, by simp [EvaluateHOL.evaluateMatch, unique, matching]⟩
    · have bad : EvaluateHOL.evaluateMatch st env value ((headPattern, headBody) :: rest) errorValue =
          (st, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateMatch, unique, EvaluateHOL.typeError]
      exact (safe st bad).elim

/-- The flat evaluator's row selection and selected-body evaluation. This
helper factors the common behavior of flat `handle` and `mat`. -/
noncomputable def flatEvaluateMatch {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (value errorValue : FlatSem.Value)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) : FlatSem.EvalResult C F :=
  match FlatSem.selectRow state rows value errorValue with
  | .error error => (state, .err error)
  | .ok (bindings, body) => FlatSem.evaluate { env with v := bindings ++ env.v } state [body]

/-- Relate source match evaluation to the corresponding flat row selection.
The body hypothesis is the expression induction hypothesis for each row,
instantiated with the pattern-related bindings. -/
theorem evaluateMatch_related {C F : Type} (genv : GlobalEnv)
    (compMap compMap2 : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (shadowers : VarN → Prop) (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (stateRel : StateRel genv sourceState flatState)
    (value errorValue : SemanticPrimitivesHOL.Value) (flatValue flatError : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (errorRel : ValueRel genv errorValue flatError)
    (rows : List (Pat × AstHOL.Exp))
    (can : canPmatchAll sourceEnv.c sourceState.refs (rows.map Prod.fst) value = true)
    (safe : ∀ next, EvaluateHOL.evaluateMatch sourceState sourceEnv value rows errorValue ≠
      (next, .err (.abort .typeError)))
    (bodySim : ∀ (pattern : Pat) (body : AstHOL.Exp)
      (bindings : List (VarN × SemanticPrimitivesHOL.Value)) (flatBindings : List (VarN × FlatSem.Value)),
      (pattern, body) ∈ rows → EnvRel genv (alistToNs bindings) flatBindings →
      ExprSim genv { compMap with v := nsBindList (patTups .none (patBindings pattern)) compMap.v } trace
        { sourceEnv with v := nsAppend (alistToNs bindings) sourceEnv.v }
        { flatEnv with v := flatBindings ++ flatEnv.v } sourceState flatState body) :
    let src := EvaluateHOL.evaluateMatch sourceState sourceEnv value rows errorValue
    let dst := flatEvaluateMatch flatEnv flatState flatValue flatError (compilePes trace compMap rows)
    EvalResultRel genv src.2 dst.2 ∧ StateRel genv src.1 dst.1 := by
  have rowRel := pmatchRows_related genv compMap compMap2 trace sourceEnv sourceState flatState shadowers
    inv mapsEq ok typesOk stateRel value flatValue valueRel rows can
  have sourceSafe := sourcePmatchRows_noTypeError sourceEnv sourceState value rows can
  cases sourceSelected : sourcePmatchRows sourceEnv sourceState value rows with
  | typeError => exact (sourceSafe sourceSelected).elim
  | noMatch =>
    rw [sourceSelected] at rowRel
    cases flatSelected : FlatSem.pmatchRows (compilePes trace compMap rows) flatState flatValue with
    | typeError => simp [flatSelected, MatchRowsRel] at rowRel
    | «match» pair => simp [flatSelected, MatchRowsRel] at rowRel
    | noMatch =>
      have sourceRun := evaluateMatch_noMatch sourceState sourceEnv value errorValue rows safe sourceSelected
      dsimp only
      rw [sourceRun]
      simp only [flatEvaluateMatch, FlatSem.selectRow, flatSelected]
      exact ⟨.raise errorRel, stateRel⟩
  | «match» selected =>
    obtain ⟨bindings, pattern, body⟩ := selected
    rw [sourceSelected] at rowRel
    cases flatSelected : FlatSem.pmatchRows (compilePes trace compMap rows) flatState flatValue with
    | typeError => simp [flatSelected, MatchRowsRel] at rowRel
    | noMatch => simp [flatSelected, MatchRowsRel] at rowRel
    | «match» flatSelectedRow =>
      obtain ⟨flatBindings, flatPattern, flatBody⟩ := flatSelectedRow
      simp only [flatSelected, MatchRowsRel] at rowRel
      obtain ⟨bindingsRel, rfl, rfl⟩ := rowRel
      obtain ⟨distinct, sourceRun⟩ := evaluateMatch_selected sourceState sourceEnv value errorValue rows
        bindings pattern body safe sourceSelected
      have member := sourcePmatchRows_mem sourceEnv sourceState value rows bindings pattern body sourceSelected
      dsimp only
      rw [sourceRun]
      simp only [flatEvaluateMatch, FlatSem.selectRow, flatSelected, compilePat_bindings, distinct, ↓reduceIte]
      simpa [ExprSim] using bodySim pattern body bindings flatBindings member bindingsRel

/-- Simulate exception handling, using the row-body induction hypotheses and
the source evaluator's non-type-error condition. -/
theorem exprSim_handle {C F : Type} (genv : GlobalEnv)
    (compMap compMap2 : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (shadowers : VarN → Prop) (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body)
    (notTypeError : ∀ next, EvaluateHOL.evaluate sourceState sourceEnv [.handle body rows] ≠
      (next, .err (.abort .typeError)))
    (rowsSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
      (pattern : Pat) (rowBody : AstHOL.Exp)
      (bindings : List (VarN × SemanticPrimitivesHOL.Value)) (flatBindings : List (VarN × FlatSem.Value)),
      (pattern, rowBody) ∈ rows → StateRel genv source flat → EnvRel genv (alistToNs bindings) flatBindings →
      ExprSim genv { compMap with v := nsBindList (patTups .none (patBindings pattern)) compMap.v } trace
        { sourceEnv with v := nsAppend (alistToNs bindings) sourceEnv.v }
        { flatEnv with v := flatBindings ++ flatEnv.v } source flat rowBody) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.handle body rows) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases related with
      | value valuesRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.value valuesRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.abort error, nextRel⟩
      | raise valueRel =>
        rename_i value flatValue
        cases can : canPmatchAll sourceEnv.c sourceNext.refs (rows.map Prod.fst) value with
        | false =>
          have bad : EvaluateHOL.evaluate sourceState sourceEnv [.handle body rows] =
              (sourceNext, .err (.abort .typeError)) := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp [can, EvaluateHOL.typeError]
          exact (notTypeError sourceNext bad).elim
        | true =>
          have safe : ∀ next, EvaluateHOL.evaluateMatch sourceNext sourceEnv value rows value ≠
              (next, .err (.abort .typeError)) := by
            intro next bad
            apply notTypeError next
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simpa [can] using bad
          have matching := evaluateMatch_related genv compMap compMap2 trace sourceEnv flatEnv sourceNext flatNext
            shadowers inv mapsEq ok typesOk nextRel value value flatValue flatValue valueRel valueRel rows can safe
            (fun pattern rowBody bindings flatBindings member bindingsRel =>
              rowsSim sourceNext flatNext pattern rowBody bindings flatBindings member nextRel bindingsRel)
          unfold ExprSim
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
          rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
            [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp only [can, ↓reduceIte]
          cases chosen : FlatSem.selectRow flatNext (compilePes trace compMap rows) flatValue flatValue with
          | error error =>
            dsimp only
            simpa [flatEvaluateMatch, chosen] using matching
          | ok pair =>
            obtain ⟨bindings, rowBody⟩ := pair
            dsimp only
            simpa [flatEvaluateMatch, chosen] using matching

/-- Simulate a case expression using the scrutinee and row-body induction
hypotheses, under the source evaluator's non-type-error condition. -/
theorem exprSim_mat {C F : Type} (genv : GlobalEnv)
    (compMap compMap2 : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (shadowers : VarN → Prop) (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body)
    (notTypeError : ∀ next, EvaluateHOL.evaluate sourceState sourceEnv [.mat body rows] ≠
      (next, .err (.abort .typeError)))
    (rowsSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
      (pattern : Pat) (rowBody : AstHOL.Exp)
      (bindings : List (VarN × SemanticPrimitivesHOL.Value)) (flatBindings : List (VarN × FlatSem.Value)),
      (pattern, rowBody) ∈ rows → StateRel genv source flat → EnvRel genv (alistToNs bindings) flatBindings →
      ExprSim genv { compMap with v := nsBindList (patTups .none (patBindings pattern)) compMap.v } trace
        { sourceEnv with v := nsAppend (alistToNs bindings) sourceEnv.v }
        { flatEnv with v := flatBindings ++ flatEnv.v } source flat rowBody) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.mat body rows) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv body values sourceRun
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              rename_i flatValue
              cases can : canPmatchAll sourceEnv.c sourceNext.refs (rows.map Prod.fst) value with
              | false =>
                have bad : EvaluateHOL.evaluate sourceState sourceEnv [.mat body rows] =
                    (sourceNext, .err (.abort .typeError)) := by
                  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
                  simp [EvaluateHOL.headValue, Flapjack.holHd, can, EvaluateHOL.typeError]
                exact (notTypeError sourceNext bad).elim
              | true =>
                have safe : ∀ next, EvaluateHOL.evaluateMatch sourceNext sourceEnv value rows bindExnV ≠
                    (next, .err (.abort .typeError)) := by
                  intro next bad
                  apply notTypeError next
                  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
                  simpa [EvaluateHOL.headValue, Flapjack.holHd, can] using bad
                have matching := evaluateMatch_related genv compMap compMap2 trace sourceEnv flatEnv sourceNext flatNext
                  shadowers inv mapsEq ok typesOk nextRel value bindExnV flatValue FlatSem.bindExnV valueRel
                  (exceptionValues_related genv ok).2.2.1 rows can safe
                  (fun pattern rowBody bindings flatBindings member bindingsRel =>
                    rowsSim sourceNext flatNext pattern rowBody bindings flatBindings member nextRel bindingsRel)
                unfold ExprSim
                rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
                rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
                  [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                simp only [EvaluateHOL.headValue, Flapjack.holHd, can, ↓reduceIte]
                change EvalResultRel genv (EvaluateHOL.evaluateMatch sourceNext sourceEnv value rows bindExnV).2
                  (match _h : FlatSem.selectRow flatNext (compilePes trace compMap rows) flatValue FlatSem.bindExnV with
                   | .error error => (flatNext, Result.err error)
                   | .ok (bindings, rowBody) => FlatSem.evaluate { flatEnv with v := bindings ++ flatEnv.v } flatNext [rowBody]).2 ∧
                  StateRel genv (EvaluateHOL.evaluateMatch sourceNext sourceEnv value rows bindExnV).1
                  (match _h : FlatSem.selectRow flatNext (compilePes trace compMap rows) flatValue FlatSem.bindExnV with
                   | .error error => (flatNext, Result.err error)
                   | .ok (bindings, rowBody) => FlatSem.evaluate { flatEnv with v := bindings ++ flatEnv.v } flatNext [rowBody]).1
                cases chosen : FlatSem.selectRow flatNext (compilePes trace compMap rows) flatValue FlatSem.bindExnV with
                | error error =>
                  dsimp only
                  simpa [flatEvaluateMatch, chosen] using matching
                | ok pair =>
                  obtain ⟨bindings, rowBody⟩ := pair
                  dsimp only
                  simpa [flatEvaluateMatch, chosen] using matching

end Flapjack.Compiler.Backend.SourceToFlat
