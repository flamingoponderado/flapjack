import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal

/-! Source-to-flat simulations and their assembly into the original
expression, match-row, and declaration correctness theorem. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant

/-- Whether a source result is an abort rather than a value or raised exception. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "abort_def"]
def resultAbort {α β : Type} (result : Result α β) : Prop :=
  match result with
  | .err (.abort _) => True
  | _ => False

namespace CompileCorrectPort

/-- The global carrier uses the reviewed canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

end CompileCorrectPort

/-- Source-to-flat simulation for expressions, match rows, and declarations. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [c, tys])]
theorem compileCorrect {C F α β : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) :
    (∀ (source : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) (sourceLast : State F)
      (result : Result (List Value) Value) (genv : GlobalEnv) (comp : Environment)
      (flatEnv : FlatSem.Environment FlatSem.Value) (flat : FlatSem.State C F)
      (flatExprs : List FlatLang.Exp) (locals trace : List VarN) (traces : List BackendCommon.Tra)
      (gen : EnvironmentGenerationStore) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)),
      EvaluateHOL.evaluate source env exprs = (sourceLast, result) ∧
      factoredInvariant interp transform gen genv idxs source flat ∧
      FactoredEnvAllRel genv comp env flatEnv locals ∧ traces.length = locals.length ∧
      envGenRel gen source.evalState ∧ result ≠ .err (.abort .typeError) ∧
      flatExprs = compileExps trace { comp with v := bindLocals traces locals comp.v } exprs →
      ∃ flatLast flatResult nextGenv,
        FlatSem.evaluate flatEnv flat flatExprs = (flatLast, flatResult) ∧
        EvalResultRel nextGenv result flatResult ∧ StateRel nextGenv sourceLast flatLast ∧
        (¬ resultAbort result → factoredInvariant interp transform gen nextGenv idxs sourceLast flatLast ∧
          envGenRel gen sourceLast.evalState ∧ oracForwardRel interp source.evalState sourceLast.evalState ∧
          finiteSubmap genv.c nextGenv.c ∧ finiteSubmap genv.tys nextGenv.tys ∧
          subglobals genv.v nextGenv.v)) ∧
    (∀ (source : State F) (env : SemEnv Value) (value : Value) (rows : List (Pat × AstHOL.Exp))
      (errorValue : Value) (genv : GlobalEnv) (comp : Environment) (sourceLast : State F)
      (result : Result (List Value) Value) (flatEnv : FlatSem.Environment FlatSem.Value)
      (flat : FlatSem.State C F) (flatValue : FlatSem.Value) (flatRows : List (FlatLang.Pat × FlatLang.Exp))
      (flatError : FlatSem.Value) (locals trace : List VarN) (traces : List BackendCommon.Tra)
      (gen : EnvironmentGenerationStore) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)),
      EvaluateHOL.evaluateMatch source env value rows errorValue = (sourceLast, result) ∧
      factoredInvariant interp transform gen genv idxs source flat ∧
      FactoredEnvAllRel genv comp env flatEnv locals ∧ ValueRel genv value flatValue ∧
      traces.length = locals.length ∧ envGenRel gen source.evalState ∧
      result ≠ .err (.abort .typeError) ∧
      flatRows = compilePes trace { comp with v := bindLocals traces locals comp.v } rows ∧
      FlatSem.pmatchRows flatRows flat flatValue ≠ .typeError ∧ ValueRel genv errorValue flatError →
      ∃ flatLast flatResult nextGenv,
        FlatProps.evaluateMatch flatEnv flat flatValue flatRows flatError = (flatLast, flatResult) ∧
        EvalResultRel nextGenv result flatResult ∧ StateRel nextGenv sourceLast flatLast ∧
        (¬ resultAbort result → factoredInvariant interp transform gen nextGenv idxs sourceLast flatLast ∧
          envGenRel gen sourceLast.evalState ∧ oracForwardRel interp source.evalState sourceLast.evalState ∧
          finiteSubmap genv.c nextGenv.c ∧ finiteSubmap genv.tys nextGenv.tys ∧
          subglobals genv.v nextGenv.v)) ∧
    (∀ (source : State F) (env : SemEnv Value) (decs : List Dec) (sourceLast : State F)
      (result : Result (SemEnv Value) Value) (path : List VarN) (n : Nat)
      (start finish : NextIndices) (other : Set (Nat × IndexKind)) (comp : Environment)
      (flat : FlatSem.State C F) (next : NextIndices) (nextComp : Environment) (flatDecs : List FlatLang.Exp)
      (n' : Nat) (genv : GlobalEnv) (gen nextGen : EnvironmentGenerationStore),
      EvaluateHOL.evaluateDecs source env decs = (sourceLast, result) ∧
      factoredInvariant interp transform gen genv (start, finish, other) source flat ∧
      compileDecs path n start comp gen decs = (n', next, nextComp, nextGen, flatDecs) ∧
      GlobalEnvInv genv comp (fun _ => False) env ∧ result ≠ .err (.abort .typeError) ∧
      envGenRel gen source.evalState ∧ envGenFutureRel interp nextGen source.evalState ∧
      idxPrev next finish →
      ∃ flatLast nextGenv flatError,
        FlatSem.evaluateDecs flat flatDecs = (flatLast, flatError) ∧ StateRel nextGenv sourceLast flatLast ∧
        (¬ resultAbort result → factoredInvariant interp transform nextGen nextGenv
          (next, finish, other) sourceLast flatLast ∧ oracForwardRel interp source.evalState sourceLast.evalState ∧
          finiteSubmap genv.c nextGenv.c ∧ finiteSubmap genv.tys nextGenv.tys ∧
          subglobals genv.v nextGenv.v) ∧
        (∀ resultEnv, result = .val resultEnv → flatError = none ∧ EnvDomainEq nextComp resultEnv ∧
          envGenRel nextGen sourceLast.evalState ∧ GlobalEnvInv nextGenv nextComp (fun _ => False) resultEnv) ∧
        (∀ error, result = .err error → ∃ flatErr, flatError = some flatErr ∧
          ResultRel (fun _ (_ : α) (_ : β) => True) nextGenv (.err error) (.err flatErr))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro source env exprs sourceLast result genv comp flatEnv flat flatExprs locals trace traces gen idxs premises
    obtain ⟨run, inv, envRel, length, generation, safe, compiled⟩ := premises
    rcases idxs with ⟨start, finish, other⟩
    subst flatExprs
    have sourceSafe : ∀ last, EvaluateHOL.evaluate source env exprs ≠ (last, .err (.abort .typeError)) := by
      intro last bad
      rw [run] at bad
      exact safe (Prod.mk.inj bad).2
    obtain ⟨nextGenv, simulation, post⟩ := factoredExpressionList_envAll interp transform exprs genv start finish other
      source flat env flatEnv locals traces trace comp gen envRel length inv generation sourceSafe
    unfold ExprListSim at simulation
    generalize flatRun : FlatSem.evaluate flatEnv flat
      (compileExps trace { comp with v := bindLocals traces locals comp.v } exprs) = flatPair at simulation post
    obtain ⟨flatLast, flatResult⟩ := flatPair
    change EvalResultRel nextGenv (EvaluateHOL.evaluate source env exprs).2 flatResult ∧
      StateRel nextGenv (EvaluateHOL.evaluate source env exprs).1 flatLast at simulation
    simp only [run] at simulation
    refine ⟨flatLast, flatResult, nextGenv, rfl, simulation.1, simulation.2, ?_⟩
    cases result with
    | val values =>
      intro _
      obtain ⟨growth, invariant, generation, forward⟩ := by simpa only [run] using post
      exact ⟨invariant, generation, forward, growth.constructors, growth.types,
        (globalGrowth_iff _ _).mp growth |>.1⟩
    | err error =>
      cases error with
      | abort error => simp [resultAbort]
      | raise value =>
        intro _
        obtain ⟨growth, invariant, generation, forward⟩ := by simpa only [run] using post
        exact ⟨invariant, generation, forward, growth.constructors, growth.types,
          (globalGrowth_iff _ _).mp growth |>.1⟩
  · intro source env value rows errorValue genv comp sourceLast result flatEnv flat flatValue flatRows flatError
      locals trace traces gen idxs premises
    obtain ⟨run, inv, envRel, valueRel, length, generation, safe, compiled, flatSafe, errorRel⟩ := premises
    rcases idxs with ⟨start, finish, other⟩
    subst flatRows
    have sourceSafe : ∀ last, EvaluateHOL.evaluateMatch source env value rows errorValue ≠
        (last, .err (.abort .typeError)) := by
      intro last bad
      rw [run] at bad
      exact safe (Prod.mk.inj bad).2
    obtain ⟨nextGenv, simulation, post⟩ := factoredEvaluateMatch_envAll interp transform genv start finish other
      source flat env flatEnv locals traces trace comp gen envRel length inv generation
      value errorValue flatValue flatError valueRel errorRel rows flatSafe sourceSafe
    generalize flatRun : flatEvaluateMatch flatEnv flat flatValue flatError
      (compilePes trace { comp with v := bindLocals traces locals comp.v } rows) = flatPair at simulation post
    obtain ⟨flatLast, flatResult⟩ := flatPair
    simp only [run] at simulation
    have target : FlatProps.evaluateMatch flatEnv flat flatValue
        (compilePes trace { comp with v := bindLocals traces locals comp.v } rows) flatError =
        (flatLast, flatResult) := by
      simpa only [flatEvaluateMatch_eq_flatProps] using flatRun
    refine ⟨flatLast, flatResult, nextGenv, target, simulation.1, simulation.2, ?_⟩
    cases result with
    | val values =>
      intro _
      obtain ⟨growth, invariant, generation, forward⟩ := by simpa only [run] using post
      exact ⟨invariant, generation, forward, growth.constructors, growth.types,
        (globalGrowth_iff _ _).mp growth |>.1⟩
    | err error =>
      cases error with
      | abort error => simp [resultAbort]
      | raise value =>
        intro _
        obtain ⟨growth, invariant, generation, forward⟩ := by simpa only [run] using post
        exact ⟨invariant, generation, forward, growth.constructors, growth.types,
          (globalGrowth_iff _ _).mp growth |>.1⟩
  · intro source env decs sourceLast result path n start finish other comp flat next nextComp flatDecs n' genv gen
      nextGen premises
    obtain ⟨run, inv, compiled, envInv, safe, generation, future, bounded⟩ := premises
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
        | abort error => simp [resultAbort]
        | raise value =>
          intro _
          obtain ⟨invariant, forward, growth⟩ := post trivial
          exact ⟨invariant, forward, growth.constructors, growth.types, (globalGrowth_iff _ _).mp growth |>.1⟩
    · intro error err
      obtain ⟨flatErr, output, related⟩ := errors error err
      refine ⟨flatErr, output, ?_⟩
      cases related with
      | raise values => exact .raise values
      | abort abort => exact .abort abort

end Flapjack.Compiler.Backend.SourceToFlat
