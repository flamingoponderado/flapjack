import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateMatch

/-! Pattern row evaluation with growing global environments. These are
preliminary simulations over relations pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Pattern matching only needs the constructor environment; the ordinary
invariant also extends over local variables when all short names are shadowed. -/
theorem globalEnvInv_local_for_patterns (genv : GlobalEnv) (baseMap : Environment)
    (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value)
    (flatLocals : List (VarN × FlatSem.Value)) (localRel : EnvRel genv sourceLocal flatLocals)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatLocals.map Prod.fst) baseEnv) :
    GlobalEnvInv genv baseMap (fun _ => True) { baseEnv with v := nsAppend sourceLocal baseEnv.v } := by
  cases envInv with
  | intro _ _ _ values constructors =>
    apply GlobalEnvInv.intro
    · intro id value fresh lookup
      cases id with
      | short name => exact (fresh ⟨name, trivial, rfl⟩).elim
      | long moduleName rest =>
        apply values (.long moduleName rest) value (by intro ⟨_, _, impossible⟩; cases impossible)
        change nsLookup (nsAppend sourceLocal baseEnv.v) (.long moduleName rest) = some value at lookup
        rw [nsLookup_append_long, envRel_no_modules genv sourceLocal flatLocals localRel moduleName] at lookup
        exact lookup
    · exact constructors

/-- Simulate selection and evaluation of an arbitrary list of pattern rows.
The all-row compatibility and row-body hypotheses are supplied by the
surrounding expression case. -/
theorem localEvaluateMatch_related {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (localRel : EnvRel genv sourceLocal flatEnv.v)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv)
    (tracesLen : traces.length = flatEnv.v.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (value errorValue : Value) (flatValue flatError : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (errorRel : ValueRel genv errorValue flatError)
    (rows : List (Pat × AstHOL.Exp))
    (can : canPmatchAll baseEnv.c source.refs (rows.map Prod.fst) value = true)
    (safe : ∀ last, EvaluateHOL.evaluateMatch source { baseEnv with v := nsAppend sourceLocal baseEnv.v }
      value rows errorValue ≠ (last, .err (.abort .typeError)))
    (each : ∀ pattern body, (pattern, body) ∈ rows → LocalEnvIH (F := F) interp transform body) :
    let sourceResult := EvaluateHOL.evaluateMatch source { baseEnv with v := nsAppend sourceLocal baseEnv.v } value rows errorValue
    let flatResult := flatEvaluateMatch flatEnv flat flatValue flatError
      (compilePes trace { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } rows)
    ∃ nextGenv, (EvalResultRel nextGenv sourceResult.2 flatResult.2 ∧ StateRel nextGenv sourceResult.1 flatResult.1) ∧
      match sourceResult.2 with
      | .err (.abort _) => True
      | _ => GlobalGrowth genv nextGenv ∧
          factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
          envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState := by
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have states := invariant.2.2.1
  have rowInv := globalEnvInv_local_for_patterns genv baseMap baseEnv sourceLocal flatEnv.v localRel envInv
  have rowRel := pmatchRows_related genv compMap baseMap trace sourceEnv source flat (fun _ => True)
    rowInv rfl invariant.1 invariant.2.1 states value flatValue valueRel rows can
  have sourceSafe := sourcePmatchRows_noTypeError sourceEnv source value rows can
  cases sourceSelected : sourcePmatchRows sourceEnv source value rows with
  | typeError => exact (sourceSafe sourceSelected).elim
  | noMatch =>
    rw [sourceSelected] at rowRel
    cases flatSelected : FlatSem.pmatchRows (compilePes trace compMap rows) flat flatValue with
    | typeError => simp [flatSelected, MatchRowsRel] at rowRel
    | «match» pair => simp [flatSelected, MatchRowsRel] at rowRel
    | noMatch =>
      have sourceRun := evaluateMatch_noMatch source sourceEnv value errorValue rows safe sourceSelected
      dsimp only [sourceEnv] at sourceRun
      dsimp only [compMap] at flatSelected
      refine ⟨genv, ?_, ?_⟩
      · simp only [sourceRun, flatEvaluateMatch, FlatSem.selectRow, flatSelected]
        exact ⟨.raise errorRel, states⟩
      · simpa [sourceRun, flatEvaluateMatch, FlatSem.selectRow, flatSelected] using
          And.intro (GlobalGrowth.refl genv) (And.intro invariant
            (And.intro generation (oracForwardRel_refl interp source.evalState)))
  | «match» selected =>
    obtain ⟨bindings, pattern, body⟩ := selected
    rw [sourceSelected] at rowRel
    cases flatSelected : FlatSem.pmatchRows (compilePes trace compMap rows) flat flatValue with
    | typeError => simp [flatSelected, MatchRowsRel] at rowRel
    | noMatch => simp [flatSelected, MatchRowsRel] at rowRel
    | «match» selectedFlat =>
      obtain ⟨flatBindings, flatPattern, flatBody⟩ := selectedFlat
      have names := flatPmatchRows_bindingNames flat flatValue (compilePes trace compMap rows)
        flatBindings flatPattern flatBody flatSelected
      simp only [flatSelected, MatchRowsRel] at rowRel
      obtain ⟨bindingsRel, rfl, rfl⟩ := rowRel
      have names : flatBindings.map Prod.fst = patBindings pattern := by simpa [compilePat_bindings] using names
      obtain ⟨distinct, sourceRun⟩ := evaluateMatch_selected source sourceEnv value errorValue rows
        bindings pattern body safe sourceSelected
      have member := sourcePmatchRows_mem sourceEnv source value rows bindings pattern body sourceSelected
      have bodySafe : ∀ last, EvaluateHOL.evaluate source
          { baseEnv with v := nsAppend (alistToNs bindings) (nsAppend sourceLocal baseEnv.v) } [body] ≠
          (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        rw [sourceRun]
        exact bad
      obtain ⟨nextGenv, bodySim, bodyPost⟩ := localEnvIH_patternBody interp transform pattern body (each pattern body member)
        genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen
        invariant generation bindings flatBindings bindingsRel names bodySafe
      dsimp only [sourceEnv] at sourceRun
      dsimp only [compMap] at flatSelected
      refine ⟨nextGenv, ?_, ?_⟩
      · simp only [sourceRun, flatEvaluateMatch, FlatSem.selectRow, flatSelected, compilePat_bindings, distinct, ↓reduceIte]
        exact bodySim
      · simp only [sourceRun, flatEvaluateMatch, FlatSem.selectRow, flatSelected, compilePat_bindings, distinct, ↓reduceIte]
        exact bodyPost

/-- Compose exception handling with the protected expression and every row
body in arbitrary related local environments. -/
theorem localEnvIH_handle {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (bodyIH : LocalEnvIH (F := F) interp transform body)
    (each : ∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvIH (F := F) interp transform rowBody) :
    LocalEnvIH (F := F) interp transform (.handle body rows) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨middleGenv, bodySim, bodyPost⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    localRel envInv tracesLen invariant generation bodySafe
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim bodyPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim bodyPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | value valueRel =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.value valueRel, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact bodyPost
  | raise valueRel =>
    rename_i value flatValue
    obtain ⟨bodyGrowth, middleInvariant, middleGeneration, bodyForward⟩ := bodyPost
    have middleLocal := envRel_growth genv middleGenv bodyGrowth sourceLocal flatEnv.v localRel
    have middleEnv := globalEnvInv_growth genv middleGenv bodyGrowth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
    cases can : canPmatchAll sourceEnv.c middleSource.refs (rows.map Prod.fst) value with
    | false =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.handle body rows] =
          (middleSource, .err (.abort .typeError)) := by
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp [can, EvaluateHOL.typeError]
      exact (safe middleSource bad).elim
    | true =>
      have rowSafe : ∀ last, EvaluateHOL.evaluateMatch middleSource sourceEnv value rows value ≠
          (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        have canBase : canPmatchAll baseEnv.c middleSource.refs (rows.map Prod.fst) value = true := can
        simpa [sourceEnv, canBase] using bad
      obtain ⟨finalGenv, matching, matchingPost⟩ := localEvaluateMatch_related interp transform middleGenv start finish other
        middleSource middleFlat baseEnv sourceLocal flatEnv traces trace baseMap gen middleLocal middleEnv tracesLen
        middleInvariant middleGeneration value value flatValue flatValue valueRel valueRel rows can rowSafe each
      have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.handle body rows] =
          EvaluateHOL.evaluateMatch middleSource sourceEnv value rows value := by
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
        simp [can]
      have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.handle body rows)] =
          flatEvaluateMatch flatEnv middleFlat flatValue flatValue (compilePes trace compMap rows) := by
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simp only
        unfold flatEvaluateMatch
        split <;> simp_all
      refine ⟨finalGenv, ?_, ?_⟩
      · unfold ExprSim
        rw [sourceOuter, flatOuter]
        exact matching
      · rw [sourceOuter, flatOuter]
        cases result : (EvaluateHOL.evaluateMatch middleSource sourceEnv value rows value).2 with
        | err error =>
          cases error with
          | abort error => simp
          | raise raised =>
            rw [result] at matchingPost
            obtain ⟨growth, finalInvariant, finalGeneration, rowForward⟩ := matchingPost
            exact ⟨bodyGrowth.trans growth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨bodyForward, rowForward⟩⟩
        | val values =>
          rw [result] at matchingPost
          obtain ⟨growth, finalInvariant, finalGeneration, rowForward⟩ := matchingPost
          exact ⟨bodyGrowth.trans growth, finalInvariant, finalGeneration,
            oracForwardRel_trans interp _ _ _ ⟨bodyForward, rowForward⟩⟩

/-- Compose pattern matching with the scrutinee and every row
body in arbitrary related local environments. -/
theorem localEnvIH_mat {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (bodyIH : LocalEnvIH (F := F) interp transform body)
    (each : ∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvIH (F := F) interp transform rowBody) :
    LocalEnvIH (F := F) interp transform (.mat body rows) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨middleGenv, bodySim, bodyPost⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    localRel envInv tracesLen invariant generation bodySafe
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim bodyPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim bodyPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact bodyPost
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatValue
        obtain ⟨bodyGrowth, middleInvariant, middleGeneration, bodyForward⟩ := bodyPost
        have middleLocal := envRel_growth genv middleGenv bodyGrowth sourceLocal flatEnv.v localRel
        have middleEnv := globalEnvInv_growth genv middleGenv bodyGrowth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
        cases can : canPmatchAll sourceEnv.c middleSource.refs (rows.map Prod.fst) value with
        | false =>
          have bad : EvaluateHOL.evaluate source sourceEnv [.mat body rows] =
              (middleSource, .err (.abort .typeError)) := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
            simp [EvaluateHOL.headValue, Flapjack.holHd, can, EvaluateHOL.typeError]
          exact (safe middleSource bad).elim
        | true =>
          have rowSafe : ∀ last, EvaluateHOL.evaluateMatch middleSource sourceEnv value rows bindExnV ≠
              (last, .err (.abort .typeError)) := by
            intro last bad
            apply safe last
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
            have canBase : canPmatchAll baseEnv.c middleSource.refs (rows.map Prod.fst) value = true := can
            simpa [sourceEnv, EvaluateHOL.headValue, Flapjack.holHd, canBase] using bad
          obtain ⟨finalGenv, matching, matchingPost⟩ := localEvaluateMatch_related interp transform middleGenv start finish other
            middleSource middleFlat baseEnv sourceLocal flatEnv traces trace baseMap gen middleLocal middleEnv tracesLen
            middleInvariant middleGeneration value bindExnV flatValue FlatSem.bindExnV valueRel (exceptionValues_related middleGenv middleInvariant.1).2.2.1 rows can rowSafe each
          have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.mat body rows] =
              EvaluateHOL.evaluateMatch middleSource sourceEnv value rows bindExnV := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
            simp [EvaluateHOL.headValue, Flapjack.holHd, can]
          have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.mat body rows)] =
              flatEvaluateMatch flatEnv middleFlat flatValue FlatSem.bindExnV (compilePes trace compMap rows) := by
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simp only
            unfold flatEvaluateMatch
            split <;> simp_all
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprSim
            rw [sourceOuter, flatOuter]
            exact matching
          · rw [sourceOuter, flatOuter]
            cases result : (EvaluateHOL.evaluateMatch middleSource sourceEnv value rows bindExnV).2 with
            | err error =>
              cases error with
              | abort error => simp
              | raise raised =>
                rw [result] at matchingPost
                obtain ⟨growth, finalInvariant, finalGeneration, rowForward⟩ := matchingPost
                exact ⟨bodyGrowth.trans growth, finalInvariant, finalGeneration,
                  oracForwardRel_trans interp _ _ _ ⟨bodyForward, rowForward⟩⟩
            | val values =>
              rw [result] at matchingPost
              obtain ⟨growth, finalInvariant, finalGeneration, rowForward⟩ := matchingPost
              exact ⟨bodyGrowth.trans growth, finalInvariant, finalGeneration,
                oracForwardRel_trans interp _ _ _ ⟨bodyForward, rowForward⟩⟩


end Flapjack.Compiler.Backend.SourceToFlat
