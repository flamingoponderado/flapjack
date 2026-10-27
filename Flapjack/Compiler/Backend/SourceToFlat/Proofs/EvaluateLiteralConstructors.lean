import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateSequence

/-! Constructor expressions with literal arguments in the preliminary
factored source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Literal lists evaluate without changing the source state. -/
theorem evaluate_literalList {F : Type} (source : State F) (env : SemEnv Value) (lits : List Lit) :
    EvaluateHOL.evaluate source env (lits.map AstHOL.Exp.lit) = (source, .val (lits.map Value.litv)) := by
  induction lits with
  | nil => simp [EvaluateHOL.evaluate]
  | cons lit rest ih =>
    cases rest with
    | nil => simp [EvaluateHOL.evaluate]
    | cons next rest =>
      cases source
      simp [EvaluateHOL.evaluate, EvaluateHOL.fixClock, EvaluateHOL.headValue, Flapjack.holHd] at ih ⊢
      rw [ih]

/-- Compiled literal lists evaluate without changing the flat state. -/
theorem flatEvaluate_literalList {C F : Type} (flat : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (trace : List VarN) (compMap : Environment) (lits : List Lit) :
    FlatSem.evaluate env flat (compileExps trace compMap (lits.map AstHOL.Exp.lit)) =
      (flat, .val (lits.map FlatSem.Value.litv)) := by
  induction lits with
  | nil => simp [compileExps, FlatSem.evaluate]
  | cons lit rest ih =>
    cases rest with
    | nil => simp [compileExps, compileExp, FlatSem.evaluate]
    | cons next rest =>
      cases flat
      simp [compileExps, compileExp, FlatSem.evaluate, FlatSem.fixClock] at ih ⊢
      rw [ih]

/-- Literal argument lists satisfy the factored expression-list relation. -/
theorem exprListSim_literals {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (source : State F) (flat : FlatSem.State C F) (lits : List Lit)
    (states : StateRel genv source flat) :
    ExprListSim genv compMap trace sourceEnv flatEnv source flat (lits.map AstHOL.Exp.lit) := by
  unfold ExprListSim
  rw [evaluate_literalList, flatEvaluate_literalList]
  refine ⟨.value ?_, states⟩
  induction lits with
  | nil => exact .nil
  | cons lit rest ih => exact .cons (.literal genv lit) ih

/-- The literal constructor arguments preserve both evaluator states. -/
theorem literalConstructor_states {C F : Type} (source : State F) (sourceEnv : SemEnv Value)
    (flat : FlatSem.State C F) (flatEnv : FlatSem.Environment FlatSem.Value)
    (trace : List VarN) (compMap : Environment) (name : Option (Ident ModN ConN)) (lits : List Lit) :
    (EvaluateHOL.evaluate source sourceEnv [.con name (lits.map AstHOL.Exp.lit)]).1 = source ∧
      (FlatSem.evaluate flatEnv flat [compileExp trace compMap (.con name (lits.map AstHOL.Exp.lit))]).1 = flat := by
  have sourceArgs := evaluate_literalList source sourceEnv lits.reverse
  have flatArgs := flatEvaluate_literalList flat flatEnv trace compMap lits.reverse
  simp only [List.map_reverse, compileExps_reverse] at sourceArgs flatArgs
  constructor
  · simp only [EvaluateHOL.evaluate]
    split
    · simp only [sourceArgs]
      cases name with
      | none => simp [buildConv]
      | some id =>
        cases lookup : nsLookup sourceEnv.c id with
        | none => simp [buildConv, lookup, EvaluateHOL.typeError]
        | some pair => cases pair; simp [buildConv, lookup]
    · simp [EvaluateHOL.typeError]
  · simp only [compileExp, FlatSem.evaluate]
    simp [flatArgs]

/-- A state-preserving expression simulation supplies the declaration
expression step without changing the global environment. -/
theorem dletExpressionStep_of_statePreserving {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (sim : ExprSim genv compMap trace sourceEnv ⟨[]⟩ source flat expr)
    (sourceSame : (EvaluateHOL.evaluate source sourceEnv [expr]).1 = source)
    (flatSame : (FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap expr]).1 = flat) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen expr := by
  refine ⟨genv, sim, ?_⟩
  cases result : (EvaluateHOL.evaluate source sourceEnv [expr]).2 with
  | val value =>
    simp only [sourceSame, flatSame]
    exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
  | err error =>
    cases error with
    | abort abort => simp
    | raise value =>
      simp only [sourceSame, flatSame]
      exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- Constructor expressions with literal arguments satisfy the declaration
expression step whenever the source execution avoids a type error. -/
theorem dletExpressionStep_literalConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : Option (Ident ModN ConN)) (lits : List Lit)
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv [.con name (lits.map AstHOL.Exp.lit)] ≠
      (last, .err (.abort .typeError))) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen
      (.con name (lits.map AstHOL.Exp.lit)) := by
  have argsSim : ExprListSim genv compMap trace sourceEnv ⟨[]⟩ source flat
      (lits.map AstHOL.Exp.lit).reverse := by
    rw [← List.map_reverse]
    exact exprListSim_literals genv compMap trace sourceEnv ⟨[]⟩ source flat lits.reverse invariant.2.2.1
  have sim : ExprSim genv compMap trace sourceEnv ⟨[]⟩ source flat (.con name (lits.map AstHOL.Exp.lit)) := by
    cases name with
    | none => exact exprSim_tuple genv compMap trace sourceEnv ⟨[]⟩ source flat _ argsSim
    | some id =>
      exact exprSim_constructor genv compMap trace sourceEnv ⟨[]⟩ source flat id _ (fun _ => False)
        envInv safe (fun _ => argsSim)
  have states := literalConstructor_states source sourceEnv flat ⟨[]⟩ trace compMap name lits
  exact dletExpressionStep_of_statePreserving interp transform genv start finish other source flat sourceEnv
    trace compMap gen _ invariant generation sim states.1 states.2

/-- A value declaration initialized by a constructor with literal arguments
satisfies the factored declaration induction hypothesis. -/
theorem factoredDecIH_dlet_literalConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat)
    (name : Option (Ident ModN ConN)) (lits : List Lit) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern (.con name (lits.map AstHOL.Exp.lit))] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv
      [.dlet location pattern (.con name (lits.map AstHOL.Exp.lit))] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern (.con name (lits.map AstHOL.Exp.lit)) flatDecs result
    sourceRun invariant compiled envInv notTypeError generation future bounded
  exact dletExpressionStep_literalConstructor interp transform genv start finish other source flat sourceEnv
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen name lits envInv invariant generation
    (dlet_expression_safe source sourceEnv location pattern _ safe)

end Flapjack.Compiler.Backend.SourceToFlat
