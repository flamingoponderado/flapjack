module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl

@[expose] public section

/-! Empty and type-abbreviation declaration cases over the preliminary
factored source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

/-- Empty source and compiler environments have the same domains. -/
theorem envDomainEq_empty : EnvDomainEq emptyEnv (⟨nsEmpty, nsEmpty⟩ : SemEnv Value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext id
    apply propext
    cases id <;> simp [emptyEnv, nsDom, nsLookup, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [emptyEnv, nsDomMod, nsLookupMod, nsEmpty]
  · funext id
    apply propext
    cases id <;> simp [emptyEnv, nsDom, nsLookup, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [emptyEnv, nsDomMod, nsLookupMod, nsEmpty]

/-- An empty declaration environment satisfies the factored global invariant. -/
theorem globalEnvInv_empty (genv : GlobalEnv) :
    GlobalEnvInv genv emptyEnv (fun _ => False) (⟨nsEmpty, nsEmpty⟩ : SemEnv Value) := by
  apply GlobalEnvInv.intro
  · intro id value _ lookup
    cases id <;> simp [nsEmpty, nsLookup] at lookup
  · intro id arity stamp lookup
    cases id <;> simp [nsEmpty, nsLookup] at lookup

/-- Declaration-conjunct outcome over the preliminary factored relations.
It is Flapjack infrastructure until those relations and evaluator carriers
have been reviewed against the HOL compiler theorem. -/
def FactoredDecCase {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source sourceLast : State F) (flat : FlatSem.State C F)
    (finish next : NextIndices) (other : Set (Nat × IndexKind)) (nextGen : EnvironmentGenerationStore)
    (nextEnv : Environment) (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value) : Prop :=
    ∃ finalState finalGenv flatError,
      FlatSem.evaluateDecs flat flatDecs = (finalState, flatError) ∧
      StateRel finalGenv sourceLast finalState ∧
      ((match result with | .err (.abort _) => False | _ => True) →
        factoredInvariant interp transform nextGen finalGenv (next, finish, other) sourceLast finalState ∧
        oracForwardRel interp source.evalState sourceLast.evalState ∧ GlobalGrowth genv finalGenv) ∧
      (∀ resultEnv, result = .val resultEnv →
        flatError = none ∧ EnvDomainEq nextEnv resultEnv ∧ envGenRel nextGen sourceLast.evalState ∧
        GlobalEnvInv finalGenv nextEnv (fun _ => False) resultEnv) ∧
      (∀ error, result = .err error → ∃ flatErr,
        flatError = some flatErr ∧
        ResultRel (fun _ (_ : SemEnv Value) (_ : Unit) => True) finalGenv (.err error) (.err flatErr))

/-- The empty-list and type-abbreviation cases share this outcome after
unfolding their compiler and evaluator equations. -/
theorem evaluateDecs_noop_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source : State F) (flat : FlatSem.State C F)
    (start finish : NextIndices) (other : Set (Nat × IndexKind)) (gen : EnvironmentGenerationStore)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    FactoredDecCase interp transform genv source source flat finish start other gen emptyEnv []
      (.val ⟨nsEmpty, nsEmpty⟩) := by
  refine ⟨flat, genv, none, ?_, invariant.2.2.1, ?_, ?_, ?_⟩
  · simp [FlatSem.evaluateDecs]
  · intro _
    exact ⟨invariant, oracForwardRel_refl interp source.evalState, GlobalGrowth.refl genv⟩
  · intro resultEnv same
    cases same
    exact ⟨rfl, envDomainEq_empty, generation, globalEnvInv_empty genv⟩
  · intro error impossible
    cases impossible

end Flapjack.Compiler.Backend.SourceToFlat
