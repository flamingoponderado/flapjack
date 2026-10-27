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
    GlobalEnvInv nextGenv compMap (fun _ => False) sourceEnv ∧
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
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    DletExpressionListStep interp transform genv start finish other source flat sourceEnv trace compMap gen
      (lits.map AstHOL.Exp.lit) := by
  refine ⟨genv, exprListSim_literals genv compMap trace sourceEnv ⟨[]⟩ source flat lits invariant.2.2.1, envInv, ?_⟩
  rw [evaluate_literalList, flatEvaluate_literalList]
  exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- A safe constructor expression inherits the growing simulation and
abort-sensitive postconditions of its right-to-left argument evaluation. -/
theorem dletExpressionStep_constructor_growing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
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
  obtain ⟨nextGenv, argsSim, nextEnvInv, post⟩ := argStep
  have sim : ExprSim nextGenv compMap trace sourceEnv ⟨[]⟩ source flat (.con name args) := by
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
    argTrace env gen name args exprSafe
    (argumentIH genv start finish other source flat sourceEnv argTrace env gen envInv invariant generation exprSafe)

end Flapjack.Compiler.Backend.SourceToFlat
