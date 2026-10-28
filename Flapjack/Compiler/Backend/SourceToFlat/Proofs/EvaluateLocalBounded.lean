import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalList
import Flapjack.EvaluateHOL.ClockFull

/-! Clock-bounded local expression and list simulation. These factored
relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- An expression simulation restricted to states at or below a clock bound. -/
def LocalEnvBoundedIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expr : AstHOL.Exp) : Prop :=
  ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore),
    source.clock ≤ limit → EnvRel genv sourceLocal flatEnv.v →
    GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv →
    traces.length = flatEnv.v.length → factoredInvariant interp transform gen genv (start, finish, other) source flat →
    envGenRel gen source.evalState →
    (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } [expr] ≠
      (last, .err (.abort .typeError))) →
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
      { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen expr

/-- An unbounded local simulation supplies every clock-bounded instance. -/
theorem localEnvBounded_of_unbounded {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expr : AstHOL.Exp) (ih : LocalEnvIH (F := F) interp transform expr) :
    LocalEnvBoundedIH (F := F) interp transform limit expr := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _
  exact ih genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen

private theorem boundedSourceEvaluate_cons {F : Type} (source : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    EvaluateHOL.evaluate source env (first :: second :: rest) =
      let head := EvaluateHOL.evaluate source env [first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := EvaluateHOL.evaluate head.1 env (second :: rest)
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (EvaluateHOL.headValue values :: values')) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [first] []).1]
  rfl

/-- Compose local expression induction hypotheses over an arbitrary list. -/
theorem boundedEnvListStep_of_each {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
      (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
      (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore),
      source.clock ≤ limit →
      EnvRel genv sourceLocal flatEnv.v →
      GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv →
      traces.length = flatEnv.v.length →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } expressions ≠
        (last, .err (.abort .typeError))) →
      LocalExpressionListStep interp transform genv start finish other source flat
        { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
        { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen expressions := by
  induction expressions with
  | nil =>
    intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ _ _ _ invariant generation _
    exact localExpressionListStep_empty interp transform genv start finish other source flat _ _ trace _ gen
      invariant generation
  | cons first rest ih =>
    intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
    let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
    let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
    cases rest with
    | nil =>
      apply localExpressionListStep_singleton
      exact each first (by simp) genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
        clockBound localRel envInv tracesLen invariant generation safe
    | cons second tail =>
      have headSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [boundedSourceEvaluate_cons, bad]
      have headStep := each first (by simp) genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
        clockBound localRel envInv tracesLen invariant generation headSafe
      change LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen (first :: second :: tail)
      apply localExpressionListStep_cons interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen first second tail headStep
      intro middleGenv middleSource middleFlat headValue headRun growth middleInvariant middleGeneration
      have tailSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv (second :: tail) ≠
          (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [boundedSourceEvaluate_cons, headRun, bad]
      apply ih
      · intro expr member
        exact each expr (List.mem_cons_of_mem _ member)
      · exact Nat.le_trans (EvaluateHOL.evaluateClockFull source middleSource sourceEnv [first] _ headRun) clockBound
      · exact envRel_growth genv middleGenv growth sourceLocal flatEnv.v localRel
      · exact globalEnvInv_growth genv middleGenv growth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
      · exact tracesLen
      · exact middleInvariant
      · exact middleGeneration
      · exact tailSafe



/-- A bounded initializer simulation supplies the bounded value-declaration
case, including arbitrary patterns and source-safe error behavior. -/
theorem factoredDecBoundedIH_dlet_expression {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (expressionIH : LocalEnvBoundedIH (F := F) interp transform limit expr) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dlet location pattern expr] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result clockBound sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  have expressionSafe := dlet_expression_safe source sourceEnv location pattern expr safe
  have emptyAppend : nsAppend nsEmpty sourceEnv.v = sourceEnv.v := by
    cases sourceEnv.v
    rfl
  have sourceEq : { sourceEnv with v := nsAppend nsEmpty sourceEnv.v } = sourceEnv := by
    simp only [emptyAppend]
  have mapEq : { env with v := bindLocals [] [] env.v } = env := by
    simp [bindLocals, nsBindList]
  have step := expressionIH genv start finish other source flat sourceEnv nsEmpty ⟨[]⟩ []
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen clockBound (.empty genv)
    (by simpa using envInv) rfl invariant generation (by simpa only [sourceEq] using expressionSafe)
  have expressionStep := (localExpressionStep_empty interp transform genv start finish other source flat sourceEnv
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen expr).mp (by simpa only [List.map_nil, sourceEq, mapEq] using step)
  exact evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern expr flatDecs result
    sourceRun invariant compiled envInv notTypeError generation future bounded expressionStep

end Flapjack.Compiler.Backend.SourceToFlat
