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

/-- Pointwise expression simulations compose into an expression-list
simulation, including intermediate state changes and errors. -/
theorem exprListSim_of_expressions {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value) (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → ∀ (source : State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat expr) :
    ∀ (source : State F) (flat : FlatSem.State C F), StateRel genv source flat →
      ExprListSim genv compMap trace sourceEnv flatEnv source flat expressions := by
  induction expressions with
  | nil =>
    intro source flat states
    simp only [ExprListSim, EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
    exact ⟨.value .nil, states⟩
  | cons head rest ih =>
    intro source flat states
    cases rest with
    | nil =>
      apply exprListSim_singleton
      exact each head (by simp) source flat states
    | cons next tail =>
      apply exprListSim_cons
      · exact each head (by simp) source flat states
      · intro nextSource nextFlat nextStates
        apply ih
        · intro expr member
          exact each expr (List.mem_cons_of_mem _ member)
        · exact nextStates

/-- If every singleton expression preserves the initial source state, their
sequential evaluation preserves it as well, including early errors. -/
theorem evaluateList_state_of_singletons {F : Type} (source : State F) (env : SemEnv Value)
    (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → (EvaluateHOL.evaluate source env [expr]).1 = source) :
    (EvaluateHOL.evaluate source env expressions).1 = source := by
  induction expressions with
  | nil => simp [EvaluateHOL.evaluate]
  | cons head rest ih =>
    cases rest with
    | nil => exact each head (by simp)
    | cons next tail =>
      have headState := each head (by simp)
      generalize headRun : EvaluateHOL.evaluate source env [head] = headResult at headState ⊢
      obtain ⟨nextState, headResult⟩ := headResult
      simp only at headState
      subst nextState
      have tailState := ih (fun expr member => each expr (List.mem_cons_of_mem _ member))
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [head] []).1, headRun]
      cases headResult with
      | err error => rfl
      | val values =>
        generalize tailRun : EvaluateHOL.evaluate source env (next :: tail) = tailResult at tailState ⊢
        obtain ⟨finalState, tailResult⟩ := tailResult
        simp only at tailState
        subst finalState
        cases tailResult <;> rfl

/-- The compiled expression list preserves its initial flat state when each
compiled singleton preserves it. -/
theorem flatEvaluateList_state_of_singletons {C F : Type} (flat : FlatSem.State C F)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment)
    (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → (FlatSem.evaluate flatEnv flat [compileExp trace compMap expr]).1 = flat) :
    (FlatSem.evaluate flatEnv flat (compileExps trace compMap expressions)).1 = flat := by
  induction expressions with
  | nil => simp [compileExps, FlatSem.evaluate]
  | cons head rest ih =>
    cases rest with
    | nil => simpa [compileExps] using each head (by simp)
    | cons next tail =>
      have headState := each head (by simp)
      generalize headRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap head] = headResult at headState ⊢
      obtain ⟨nextState, headResult⟩ := headResult
      simp only at headState
      subst nextState
      have tailState := ih (fun expr member => each expr (List.mem_cons_of_mem _ member))
      simp only [compileExps]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap head] (FlatLang.Exp.lit .none (.intLit 0)) []).1, headRun]
      cases headResult with
      | err error => rfl
      | val values =>
        simp only [compileExps] at tailState
        generalize tailRun : FlatSem.evaluate flatEnv flat
          (compileExp trace compMap next :: compileExps trace compMap tail) = tailResult at tailState ⊢
        obtain ⟨finalState, tailResult⟩ := tailResult
        simp only at tailState
        subst finalState
        cases tailResult <;> rfl

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

/-- If a constructor's argument list preserves both evaluator states, the
constructor expression itself also preserves them, including error paths. -/
theorem constructor_states_of_args {C F : Type} (source : State F) (sourceEnv : SemEnv Value)
    (flat : FlatSem.State C F) (flatEnv : FlatSem.Environment FlatSem.Value)
    (trace : List VarN) (compMap : Environment) (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (sourceSame : (EvaluateHOL.evaluate source sourceEnv args.reverse).1 = source)
    (flatSame : (FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse).1 = flat) :
    (EvaluateHOL.evaluate source sourceEnv [.con name args]).1 = source ∧
      (FlatSem.evaluate flatEnv flat [compileExp trace compMap (.con name args)]).1 = flat := by
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at sourceSame ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  simp only at sourceSame
  subst sourceNext
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at flatSame ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  simp only at flatSame
  subst flatNext
  constructor
  · simp only [EvaluateHOL.evaluate]
    split
    · simp only [sourceRun]
      cases sourceResult with
      | err error => rfl
      | val values =>
        cases name with
        | none => simp [buildConv]
        | some id =>
          cases lookup : nsLookup sourceEnv.c id with
          | none => simp [buildConv, lookup, EvaluateHOL.typeError]
          | some pair => cases pair; simp [buildConv, lookup]
    · simp [EvaluateHOL.typeError]
  · simp only [compileExp, FlatSem.evaluate, flatRun]
    cases flatResult <;> rfl

/-- A constructor with an arbitrary state-preserving argument-list
simulation satisfies the factored declaration expression step. -/
theorem dletExpressionStep_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv [.con name args] ≠ (last, .err (.abort .typeError)))
    (argsSim : ExprListSim genv compMap trace sourceEnv ⟨[]⟩ source flat args.reverse)
    (sourceSame : (EvaluateHOL.evaluate source sourceEnv args.reverse).1 = source)
    (flatSame : (FlatSem.evaluate ⟨[]⟩ flat (compileExps trace compMap args).reverse).1 = flat) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen (.con name args) := by
  have sim : ExprSim genv compMap trace sourceEnv ⟨[]⟩ source flat (.con name args) := by
    cases name with
    | none => exact exprSim_tuple genv compMap trace sourceEnv ⟨[]⟩ source flat args argsSim
    | some id =>
      exact exprSim_constructor genv compMap trace sourceEnv ⟨[]⟩ source flat id args (fun _ => False)
        envInv safe (fun _ => argsSim)
  have states := constructor_states_of_args source sourceEnv flat ⟨[]⟩ trace compMap name args sourceSame flatSame
  exact dletExpressionStep_of_statePreserving interp transform genv start finish other source flat sourceEnv
    trace compMap gen _ invariant generation sim states.1 states.2

/-- Individual expression simulations and state-preservation facts compose
into the constructor case, in the source's right-to-left argument order. -/
theorem dletExpressionStep_constructor_of_expressions {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv [.con name args] ≠ (last, .err (.abort .typeError)))
    (eachSim : ∀ expr, expr ∈ args → ∀ (s : State F) (f : FlatSem.State C F),
      StateRel genv s f → ExprSim genv compMap trace sourceEnv ⟨[]⟩ s f expr)
    (eachSource : ∀ expr, expr ∈ args → (EvaluateHOL.evaluate source sourceEnv [expr]).1 = source)
    (eachFlat : ∀ expr, expr ∈ args → (FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap expr]).1 = flat) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen (.con name args) := by
  apply dletExpressionStep_constructor interp transform genv start finish other source flat sourceEnv trace compMap
    gen name args envInv invariant generation safe
  · apply exprListSim_of_expressions genv compMap trace sourceEnv ⟨[]⟩ args.reverse
    · intro expr member
      exact eachSim expr (List.mem_reverse.mp member)
    · exact invariant.2.2.1
  · apply evaluateList_state_of_singletons source sourceEnv args.reverse
    intro expr member
    exact eachSource expr (List.mem_reverse.mp member)
  · rw [← compileExps_reverse]
    apply flatEvaluateList_state_of_singletons flat ⟨[]⟩ trace compMap args.reverse
    intro expr member
    exact eachFlat expr (List.mem_reverse.mp member)

/-- Constructor arguments that create literals or closures without changing
either evaluator state. -/
def pureConstructorArgument : Lit ⊕ (VarN × AstHOL.Exp) → AstHOL.Exp
  | .inl lit => .lit lit
  | .inr (name, body) => .fn name body

/-- Constructors can combine literal and closure arguments while preserving
the declaration expression invariant. -/
theorem dletExpressionStep_pureConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : Option (Ident ModN ConN)) (args : List (Lit ⊕ (VarN × AstHOL.Exp)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv [.con name (args.map pureConstructorArgument)] ≠
      (last, .err (.abort .typeError))) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen
      (.con name (args.map pureConstructorArgument)) := by
  apply dletExpressionStep_constructor_of_expressions interp transform genv start finish other source flat sourceEnv
    trace compMap gen name (args.map pureConstructorArgument) envInv invariant generation safe
  · intro expr member s f states
    obtain ⟨arg, _, rfl⟩ := List.mem_map.mp member
    cases arg with
    | inl lit => exact exprSim_literal genv compMap trace sourceEnv ⟨[]⟩ s f states lit
    | inr pair =>
      obtain ⟨argName, body⟩ := pair
      have related := (evaluate_global_function_related genv compMap sourceEnv envInv s f states trace argName body 0).2.2.1
      simp only [pureConstructorArgument, ExprSim, EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
      exact ⟨.value (.cons related .nil), states⟩
  · intro expr member
    obtain ⟨arg, _, rfl⟩ := List.mem_map.mp member
    cases arg with
    | inl lit => simp [pureConstructorArgument, EvaluateHOL.evaluate]
    | inr pair => cases pair; simp [pureConstructorArgument, EvaluateHOL.evaluate]
  · intro expr member
    obtain ⟨arg, _, rfl⟩ := List.mem_map.mp member
    cases arg with
    | inl lit => simp [pureConstructorArgument, compileExp, FlatSem.evaluate]
    | inr pair => cases pair; simp [pureConstructorArgument, compileExp, FlatSem.evaluate]

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
  apply dletExpressionStep_constructor interp transform genv start finish other source flat sourceEnv trace compMap
    gen name (lits.map AstHOL.Exp.lit) envInv invariant generation safe argsSim
  · rw [← List.map_reverse, evaluate_literalList]
  · rw [← compileExps_reverse, ← List.map_reverse, flatEvaluate_literalList]

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

/-- Value declarations initialized with literal and closure constructor
arguments satisfy the factored declaration induction hypothesis. -/
theorem factoredDecIH_dlet_pureConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat)
    (name : Option (Ident ModN ConN)) (args : List (Lit ⊕ (VarN × AstHOL.Exp))) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern (.con name (args.map pureConstructorArgument))] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv
      [.dlet location pattern (.con name (args.map pureConstructorArgument))] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern (.con name (args.map pureConstructorArgument)) flatDecs result
    sourceRun invariant compiled envInv notTypeError generation future bounded
  exact dletExpressionStep_pureConstructor interp transform genv start finish other source flat sourceEnv
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen name args envInv invariant generation
    (dlet_expression_safe source sourceEnv location pattern _ safe)

end Flapjack.Compiler.Backend.SourceToFlat
