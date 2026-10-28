import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLiteralConstructors

/-! Constructor composition for argument lists that may change state and
grow the preliminary factored global environment. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Argument-list induction hypothesis with abort-sensitive invariant and
oracle postconditions. The factored relations still need HOL review. -/
def DletExpressionListStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (args : List AstHOL.Exp) : Prop :=
  let sourceResult := EvaluateHOL.evaluate source sourceEnv args
  let flatResult := FlatSem.evaluate ⟨[]⟩ flat (compileExps trace compMap args)
  ∃ nextGenv, ExprListSim nextGenv compMap trace sourceEnv ⟨[]⟩ source flat args ∧
    match sourceResult.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
        envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState

/-- Literal lists establish the growing argument-list hypothesis without
changing either evaluator state or the global environment. -/
theorem dletExpressionListStep_literals {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (lits : List Lit)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen
      (lits.map AstHOL.Exp.lit) := by
  refine ⟨genv, exprListSim_literals genv compMap trace sourceEnv ⟨[]⟩ source flat lits invariant.2.2.1, ?_⟩
  rw [evaluate_literalList, flatEvaluate_literalList]
  exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- A singleton expression step supplies the corresponding list step. -/
theorem dletExpressionListStep_singleton {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp)
    (step : DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen expr) :
    DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen [expr] := by
  obtain ⟨nextGenv, sim, post⟩ := step
  refine ⟨nextGenv, exprListSim_singleton nextGenv compMap trace sourceEnv ⟨[]⟩ source flat expr sim, ?_⟩
  cases result : (EvaluateHOL.evaluate source sourceEnv [expr]).2 with
  | val value => simpa only [result, compileExps] using post
  | err error =>
    cases error with
    | abort error => simp
    | raise value => simpa only [result, compileExps] using post

/-- The empty argument list establishes the growing list hypothesis. -/
theorem dletExpressionListStep_empty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen [] := by
  simpa using dletExpressionListStep_literals interp transform genv start finish other source flat sourceEnv trace
    compMap gen [] invariant generation

private theorem sourceEvaluate_cons {F : Type} (source : State F) (env : SemEnv Value)
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

private theorem flatEvaluate_cons {C F : Type} (flat : FlatSem.State C F) (trace : List VarN)
    (compMap : Environment) (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    FlatSem.evaluate ⟨[]⟩ flat (compileExps trace compMap (first :: second :: rest)) =
      let head := FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := FlatSem.evaluate ⟨[]⟩ head.1 (compileExps trace compMap (second :: rest))
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (@Flapjack.holHd FlatSem.Value ⟨FlatSem.unitValue⟩ values :: values')) := by
  simp only [compileExps]
  rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
    [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1]
  rfl

/-- Sequential composition of a growing expression step and the growing
induction hypothesis for a nonempty tail. -/
theorem dletExpressionListStep_cons {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (headStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen first)
    (tailIH : ∀ (middleGenv : GlobalEnv) (middleSource : State F) (middleFlat : FlatSem.State C F)
      (headValue : Value), EvaluateHOL.evaluate source sourceEnv [first] = (middleSource, .val [headValue]) →
      GlobalEnvInv middleGenv compMap (fun _ => False) sourceEnv →
      factoredInvariant interp transform gen middleGenv (start, finish, other) middleSource middleFlat →
      envGenRel gen middleSource.evalState →
      DletExpressionListStep interp transform middleGenv start finish other middleSource middleFlat
        sourceEnv trace compMap gen (second :: rest)) :
    DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen
      (first :: second :: rest) := by
  obtain ⟨middleGenv, headSim, headPost⟩ := headStep
  unfold ExprSim at headSim
  generalize sourceHead : EvaluateHOL.evaluate source sourceEnv [first] = sourceHeadResult at headSim headPost
  obtain ⟨middleSource, sourceHeadResult⟩ := sourceHeadResult
  generalize flatHead : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap first] = flatHeadResult at headSim headPost
  obtain ⟨middleFlat, flatHeadResult⟩ := flatHeadResult
  obtain ⟨headRelated, headStates⟩ := headSim
  cases headRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprListSim
      rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
      exact ⟨.abort error, headStates⟩
    · rw [sourceEvaluate_cons, sourceHead]
      trivial
  | raise headValue =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprListSim
      rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
      exact ⟨.raise headValue, headStates⟩
    · rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
      exact headPost
  | @value sourceValues flatValues headValues =>
    obtain ⟨sourceValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv first sourceValues sourceHead
    subst sourceValues
    cases headValues with
    | cons headValue tailValues =>
      cases tailValues with
      | nil =>
        obtain ⟨headGrowth, middleInvariant, middleGeneration, headForward⟩ := headPost
        have middleEnv := globalEnvInv_growth genv middleGenv headGrowth compMap (fun _ => False) sourceEnv envInv
        obtain ⟨finalGenv, tailSim, tailPost⟩ := tailIH middleGenv middleSource middleFlat sourceValue sourceHead middleEnv
          middleInvariant middleGeneration
        unfold ExprListSim at tailSim
        generalize sourceTail : EvaluateHOL.evaluate middleSource sourceEnv (second :: rest) = sourceTailResult at tailSim tailPost
        obtain ⟨finalSource, sourceTailResult⟩ := sourceTailResult
        generalize flatTail : FlatSem.evaluate ⟨[]⟩ middleFlat (compileExps trace compMap (second :: rest)) = flatTailResult at tailSim tailPost
        obtain ⟨finalFlat, flatTailResult⟩ := flatTailResult
        obtain ⟨tailRelated, tailStates⟩ := tailSim
        cases tailRelated with
        | abort error =>
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨.abort error, tailStates⟩
          · simp only [sourceEvaluate_cons, sourceHead, sourceTail]
        | raise tailValue =>
          obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨.raise tailValue, tailStates⟩
          · simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩
        | value tailValues =>
          obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            exact ⟨.value (.cons (valueRel_growth middleGenv finalGenv tailGrowth _ _ headValue) tailValues), tailStates⟩
          · simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩

/-- The factored expression induction hypothesis, parametrized over all
states and the ordinary source non-type-error premise. -/
def FactoredExpressionIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (expr : AstHOL.Exp) : Prop :=
  ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore),
    GlobalEnvInv genv compMap (fun _ => False) sourceEnv →
    factoredInvariant interp transform gen genv (start, finish, other) source flat →
    envGenRel gen source.evalState →
    (∀ last, EvaluateHOL.evaluate source sourceEnv [expr] ≠ (last, .err (.abort .typeError))) →
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen expr

/-- Expression induction hypotheses compose over arbitrary source lists;
safety of the head and each reached tail follows from safety of the list. -/
theorem dletExpressionListStep_of_each {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → FactoredExpressionIH (F := F) interp transform expr) :
    ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
      (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore),
      GlobalEnvInv genv compMap (fun _ => False) sourceEnv →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source sourceEnv expressions ≠ (last, .err (.abort .typeError))) →
      DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen expressions := by
  induction expressions with
  | nil =>
    intro genv start finish other source flat sourceEnv trace compMap gen _ invariant generation _
    exact dletExpressionListStep_empty interp transform genv start finish other source flat sourceEnv trace compMap gen
      invariant generation
  | cons first rest ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    cases rest with
    | nil =>
      apply dletExpressionListStep_singleton
      exact each first (by simp) genv start finish other source flat sourceEnv trace compMap gen
        envInv invariant generation safe
    | cons second tail =>
      have headSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        simp only [sourceEvaluate_cons, bad]
      have headStep := each first (by simp) genv start finish other source flat sourceEnv trace compMap gen
        envInv invariant generation headSafe
      apply dletExpressionListStep_cons interp transform genv start finish other source flat sourceEnv trace compMap gen
        first second tail envInv headStep
      intro middleGenv middleSource middleFlat headValue headRun middleEnv middleInvariant middleGeneration
      have tailSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv (second :: tail) ≠
          (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        simp only [sourceEvaluate_cons, headRun, bad]
      apply ih
      · intro expr member
        exact each expr (List.mem_cons_of_mem _ member)
      · exact middleEnv
      · exact middleInvariant
      · exact middleGeneration
      · exact tailSafe

/-- An aborted argument evaluation makes the constructor abort with the
same related states, without needing a post-abort environment relation. -/
theorem exprSim_constructor_abort {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (source : State F) (flat : FlatSem.State C F) (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (check : doConCheck sourceEnv.c name args.length = true)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv source flat args.reverse)
    (nextSource : State F) (error : Abort)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = (nextSource, .err (.abort error))) :
    ExprSim genv compMap trace sourceEnv flatEnv source flat (.con name args) := by
  unfold ExprListSim at argsSim
  rw [compileExps_reverse, sourceRun] at argsSim
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = result at argsSim
  obtain ⟨nextFlat, flatResult⟩ := result
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort =>
    unfold ExprSim
    rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
    simp only [check, if_true, sourceRun, flatRun]
    exact ⟨.abort error, states⟩

/-- A safe constructor expression inherits the growing simulation and
abort-sensitive postconditions of its right-to-left argument evaluation. -/
theorem dletExpressionStep_constructor_growing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (safe : ∀ last, EvaluateHOL.evaluate source sourceEnv [.con name args] ≠ (last, .err (.abort .typeError)))
    (argStep : DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen
      args.reverse) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen (.con name args) := by
  have check : doConCheck sourceEnv.c name args.length = true := by
    cases h : doConCheck sourceEnv.c name args.length with
    | true => rfl
    | false =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con name args] = (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, h, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  obtain ⟨nextGenv, argsSim, post⟩ := argStep
  have sim : ExprSim nextGenv compMap trace sourceEnv ⟨[]⟩ source flat (.con name args) := by
    generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = result at post
    obtain ⟨nextSource, result⟩ := result
    cases result with
    | err error =>
      cases error with
      | abort abort =>
        exact exprSim_constructor_abort nextGenv compMap trace sourceEnv ⟨[]⟩ source flat name args
          check argsSim nextSource abort sourceRun
      | raise value =>
        have growth : GlobalGrowth genv nextGenv := post.1
        have nextEnvInv := globalEnvInv_growth genv nextGenv growth compMap (fun _ => False) sourceEnv envInv
        cases name with
        | none => exact exprSim_tuple nextGenv compMap trace sourceEnv ⟨[]⟩ source flat args argsSim
        | some id =>
          exact exprSim_constructor nextGenv compMap trace sourceEnv ⟨[]⟩ source flat id args
            (fun _ => False) nextEnvInv safe (fun _ => argsSim)
    | val values =>
      have growth : GlobalGrowth genv nextGenv := post.1
      have nextEnvInv := globalEnvInv_growth genv nextGenv growth compMap (fun _ => False) sourceEnv envInv
      cases name with
      | none => exact exprSim_tuple nextGenv compMap trace sourceEnv ⟨[]⟩ source flat args argsSim
      | some id =>
        exact exprSim_constructor nextGenv compMap trace sourceEnv ⟨[]⟩ source flat id args
          (fun _ => False) nextEnvInv safe (fun _ => argsSim)
  refine ⟨nextGenv, sim, ?_⟩
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate ⟨[]⟩ flat (compileExps trace compMap args).reverse = flatResult at argsSim post ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨related, _⟩ := argsSim
  cases related with
  | abort error =>
    simp [EvaluateHOL.evaluate, check, sourceRun]
  | raise related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, check, sourceRun, flatRun] using post
  | @value sourceValues flatValues related =>
    cases built : buildConv sourceEnv.c name sourceValues.reverse with
    | none =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con name args] =
          (sourceNext, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, check, sourceRun, built, EvaluateHOL.typeError]
      exact False.elim (safe sourceNext bad)
    | some value =>
      simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, check, sourceRun, flatRun, built] using post

/-- The constructor expression induction case follows from the induction
hypotheses for its arguments, including state-changing arguments. -/
theorem factoredExpressionIH_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → FactoredExpressionIH (F := F) interp transform expr) :
    FactoredExpressionIH (F := F) interp transform (.con name args) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have check : doConCheck sourceEnv.c name args.length = true := by
    cases h : doConCheck sourceEnv.c name args.length with
    | true => rfl
    | false =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con name args] = (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, h, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    simp [EvaluateHOL.evaluate, check, bad]
  have argsStep := dletExpressionListStep_of_each interp transform args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat sourceEnv
    trace compMap gen envInv invariant generation argsSafe
  exact dletExpressionStep_constructor_growing interp transform genv start finish other source flat sourceEnv
    trace compMap gen name args envInv safe argsStep

/-- A value declaration follows from the factored induction hypothesis for
its initializer expression. -/
theorem factoredDecIH_dlet_expression {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (expressionIH : FactoredExpressionIH (F := F) interp transform expr) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern expr] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern expr flatDecs result
    sourceRun invariant compiled envInv notTypeError generation future bounded
  exact expressionIH genv start finish other source flat sourceEnv ((AstHOL.patBindings pattern).reverse ++ trace)
    env gen envInv invariant generation (dlet_expression_safe source sourceEnv location pattern expr safe)

/-- Source expressions covered by the current factored induction, including
arbitrarily nested constructors and annotations around the existing simple
forms. -/
inductive FactoredConstructorExpression : AstHOL.Exp → Prop where
  | simple (expr : AstHOL.Exp) : FactoredSimpleExpression expr → FactoredConstructorExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredConstructorExpression expr) → FactoredConstructorExpression (.con name args)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredConstructorExpression expr →
      FactoredConstructorExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredConstructorExpression expr →
      FactoredConstructorExpression (.lannot expr loc)

/-- Covered nested constructor expressions satisfy the factored expression
induction hypothesis. -/
theorem factoredExpressionIH_constructorTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredConstructorExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | simple expr supported =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    exact factoredSimpleExpression_step interp transform genv start finish other source flat sourceEnv trace compMap
      gen expr supported envInv invariant generation safe
  | constructor name args _ ih =>
    exact factoredExpressionIH_constructor interp transform name args ih
  | tannot expr typ _ ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    apply dletExpressionStep_tannot interp transform genv start finish other source flat sourceEnv trace compMap gen expr typ
    apply ih genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  | lannot expr loc _ ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    apply dletExpressionStep_lannot interp transform genv start finish other source flat sourceEnv trace compMap gen expr loc
    apply ih genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad

/-- Declaration-level constructor case from a growing argument-list
induction hypothesis. This is factored infrastructure, not the HOL theorem. -/
theorem factoredDecIH_dlet_constructor_growing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (argumentIH : ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
      (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore),
      GlobalEnvInv genv compMap (fun _ => False) sourceEnv →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source sourceEnv [.con name args] ≠ (last, .err (.abort .typeError))) →
      DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen args.reverse) :
    FactoredDecIH (F := F) interp transform [.dlet location pattern (.con name args)] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern (.con name args)] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  have exprSafe := dlet_expression_safe source sourceEnv location pattern (.con name args) safe
  let argTrace := (AstHOL.patBindings pattern).reverse ++ trace
  apply evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern (.con name args) flatDecs result
    sourceRun invariant compiled envInv notTypeError generation future bounded
  exact dletExpressionStep_constructor_growing interp transform genv start finish other source flat sourceEnv
    argTrace env gen name args envInv exprSafe
    (argumentIH genv start finish other source flat sourceEnv argTrace env gen envInv invariant generation exprSafe)

end Flapjack.Compiler.Backend.SourceToFlat
