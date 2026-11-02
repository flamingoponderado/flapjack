import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal

/-! Source-shaped source-to-flat simulations. These are Flapjack proof
infrastructure pending review of the source and flat evaluators. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant

/-- An error-only result relation is independent of its unused success types. -/
theorem resultRel_error_change_payload {α β γ δ : Type} (g : GlobalEnv)
    (source : ErrorResult Value) (flat : ErrorResult FlatSem.Value)
    (related : ResultRel (fun _ (_ : α) (_ : β) => True) g (.err source) (.err flat)) :
    ResultRel (fun _ (_ : γ) (_ : δ) => True) g (.err source) (.err flat) := by
  cases related with
  | raise h => exact .raise h
  | abort error => exact .abort error

/-- The expression-list simulation with the source theorem's compiled-output
equality and explicit map and global-growth conclusions. -/
theorem sourceCompileCorrect_expressions {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source sourceLast : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp)
    (result : Result (List Value) Value) (genv : GlobalEnv) (comp : Environment)
    (flatEnv : FlatSem.Environment FlatSem.Value) (flat : FlatSem.State C F)
    (flatExprs : List FlatLang.Exp) (locals : List VarN) (trace : List VarN)
    (traces : List BackendCommon.Tra) (gen : EnvironmentGenerationStore)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (run : EvaluateHOL.evaluate source env exprs = (sourceLast, result))
    (inv : factoredInvariant interp transform gen genv idxs source flat)
    (envRel : FactoredEnvAllRel genv comp env flatEnv locals)
    (length : traces.length = locals.length) (generation : envGenRel gen source.evalState)
    (safe : result ≠ .err (.abort .typeError))
    (compiled : flatExprs = compileExps trace { comp with v := bindLocals traces locals comp.v } exprs) :
    ∃ flatLast flatResult nextGenv,
      FlatSem.evaluate flatEnv flat flatExprs = (flatLast, flatResult) ∧
      EvalResultRel nextGenv result flatResult ∧ StateRel nextGenv sourceLast flatLast ∧
      ((match result with | .err (.abort _) => False | _ => True) →
        factoredInvariant interp transform gen nextGenv idxs sourceLast flatLast ∧
        envGenRel gen sourceLast.evalState ∧ oracForwardRel interp source.evalState sourceLast.evalState ∧
        finiteSubmap genv.c nextGenv.c ∧ finiteSubmap genv.tys nextGenv.tys ∧
        subglobals genv.v nextGenv.v) := by
  rcases idxs with ⟨start, finish, other⟩
  subst flatExprs
  obtain ⟨flatLast, flatResult, nextGenv, target, results, states, post⟩ :=
    factoredCompileExpressions interp transform exprs genv start finish other source sourceLast flat env
      flatEnv locals traces trace comp gen result run envRel length inv generation safe
  refine ⟨flatLast, flatResult, nextGenv, target, results, states, ?_⟩
  cases result with
  | val values =>
    intro _
    obtain ⟨growth, invariant, generation, forward⟩ := post
    exact ⟨invariant, generation, forward, growth.constructors, growth.types,
      (globalGrowth_iff _ _).mp growth |>.1⟩
  | err error =>
    cases error with
    | abort error => simp
    | raise value =>
      intro _
      obtain ⟨growth, invariant, generation, forward⟩ := post
      exact ⟨invariant, generation, forward, growth.constructors, growth.types,
        (globalGrowth_iff _ _).mp growth |>.1⟩

/-- The match-row simulation with the source theorem's compiled-output,
pattern-safety, and explicit map and global-growth conclusions. -/
theorem sourceCompileCorrect_match {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source sourceLast : State F) (env : SemEnv Value) (value errorValue : Value)
    (rows : List (Pat × AstHOL.Exp)) (result : Result (List Value) Value)
    (genv : GlobalEnv) (comp : Environment) (flatEnv : FlatSem.Environment FlatSem.Value)
    (flat : FlatSem.State C F) (flatValue flatError : FlatSem.Value)
    (flatRows : List (FlatLang.Pat × FlatLang.Exp)) (locals : List VarN) (trace : List VarN)
    (traces : List BackendCommon.Tra) (gen : EnvironmentGenerationStore)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (run : EvaluateHOL.evaluateMatch source env value rows errorValue = (sourceLast, result))
    (inv : factoredInvariant interp transform gen genv idxs source flat)
    (envRel : FactoredEnvAllRel genv comp env flatEnv locals) (valueRel : ValueRel genv value flatValue)
    (length : traces.length = locals.length) (generation : envGenRel gen source.evalState)
    (safe : result ≠ .err (.abort .typeError))
    (compiled : flatRows = compilePes trace { comp with v := bindLocals traces locals comp.v } rows)
    (flatSafe : FlatSem.pmatchRows flatRows flat flatValue ≠ .typeError)
    (errorRel : ValueRel genv errorValue flatError) :
    ∃ flatLast flatResult nextGenv,
      FlatProps.evaluateMatch flatEnv flat flatValue flatRows flatError = (flatLast, flatResult) ∧
      EvalResultRel nextGenv result flatResult ∧ StateRel nextGenv sourceLast flatLast ∧
      ((match result with | .err (.abort _) => False | _ => True) →
        factoredInvariant interp transform gen nextGenv idxs sourceLast flatLast ∧
        envGenRel gen sourceLast.evalState ∧ oracForwardRel interp source.evalState sourceLast.evalState ∧
        finiteSubmap genv.c nextGenv.c ∧ finiteSubmap genv.tys nextGenv.tys ∧
        subglobals genv.v nextGenv.v) := by
  rcases idxs with ⟨start, finish, other⟩
  subst flatRows
  obtain ⟨flatLast, flatResult, nextGenv, target, results, states, post⟩ :=
    factoredCompileMatch interp transform genv start finish other source sourceLast flat env flatEnv locals
      traces trace comp gen value errorValue flatValue flatError rows result run envRel length inv generation
      valueRel errorRel flatSafe safe
  have target' : FlatProps.evaluateMatch flatEnv flat flatValue
      (compilePes trace { comp with v := bindLocals traces locals comp.v } rows) flatError =
      (flatLast, flatResult) := by
    simpa only [flatEvaluateMatch_eq_flatProps] using target
  refine ⟨flatLast, flatResult, nextGenv, target', results, states, ?_⟩
  cases result with
  | val values =>
    intro _
    obtain ⟨growth, invariant, generation, forward⟩ := post
    exact ⟨invariant, generation, forward, growth.constructors, growth.types,
      (globalGrowth_iff _ _).mp growth |>.1⟩
  | err error =>
    cases error with
    | abort error => simp
    | raise value =>
      intro _
      obtain ⟨growth, invariant, generation, forward⟩ := post
      exact ⟨invariant, generation, forward, growth.constructors, growth.types,
        (globalGrowth_iff _ _).mp growth |>.1⟩

/-- The declaration-list simulation with independently polymorphic unused
success types in the error-result relation, as in the source theorem. -/
theorem sourceCompileCorrect_declarations {C F α β : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source sourceLast : State F) (env : SemEnv Value) (decs : List Dec)
    (result : Result (SemEnv Value) Value) (path : List VarN) (n n' : Nat)
    (start finish next : NextIndices) (other : Set (Nat × IndexKind))
    (comp nextComp : Environment) (flat : FlatSem.State C F) (flatDecs : List FlatLang.Exp)
    (genv : GlobalEnv) (gen nextGen : EnvironmentGenerationStore)
    (run : EvaluateHOL.evaluateDecs source env decs = (sourceLast, result))
    (inv : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs path n start comp gen decs = (n', next, nextComp, nextGen, flatDecs))
    (envInv : GlobalEnvInv genv comp (fun _ => False) env) (safe : result ≠ .err (.abort .typeError))
    (generation : envGenRel gen source.evalState) (future : envGenFutureRel interp nextGen source.evalState)
    (bounded : idxPrev next finish) :
    ∃ flatLast nextGenv flatError,
      FlatSem.evaluateDecs flat flatDecs = (flatLast, flatError) ∧ StateRel nextGenv sourceLast flatLast ∧
      ((match result with | .err (.abort _) => False | _ => True) →
        factoredInvariant interp transform nextGen nextGenv (next, finish, other) sourceLast flatLast ∧
        oracForwardRel interp source.evalState sourceLast.evalState ∧
        finiteSubmap genv.c nextGenv.c ∧ finiteSubmap genv.tys nextGenv.tys ∧
        subglobals genv.v nextGenv.v) ∧
      (∀ resultEnv, result = .val resultEnv → flatError = none ∧ EnvDomainEq nextComp resultEnv ∧
        envGenRel nextGen sourceLast.evalState ∧ GlobalEnvInv nextGenv nextComp (fun _ => False) resultEnv) ∧
      (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
        ResultRel (fun _ (_ : α) (_ : β) => True) nextGenv (.err error) (.err flatErr)) := by
  obtain ⟨flatLast, nextGenv, flatError, target, states, post, success, errors⟩ :=
    factoredCompileDeclarations interp transform decs genv comp nextComp env path source sourceLast flat
      start finish next other n n' gen nextGen flatDecs result run inv compiled envInv safe generation future bounded
  refine ⟨flatLast, nextGenv, flatError, target, states, ?_, success, ?_⟩
  · cases result with
    | val values =>
      intro _
      obtain ⟨invariant, forward, growth⟩ := post trivial
      exact ⟨invariant, forward, growth.constructors, growth.types, (globalGrowth_iff _ _).mp growth |>.1⟩
    | err error =>
      cases error with
      | abort error => simp
      | raise value =>
        intro _
        obtain ⟨invariant, forward, growth⟩ := post trivial
        exact ⟨invariant, forward, growth.constructors, growth.types, (globalGrowth_iff _ _).mp growth |>.1⟩
  · intro error err
    obtain ⟨flatErr, output, related⟩ := errors error err
    exact ⟨flatErr, output, resultRel_error_change_payload nextGenv error flatErr related⟩

end Flapjack.Compiler.Backend.SourceToFlat
