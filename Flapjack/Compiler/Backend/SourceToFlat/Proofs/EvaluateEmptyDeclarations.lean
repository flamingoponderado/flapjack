import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl

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

/-- A declaration list whose source and compiler equations are both empty
has the factored compiler outcome. The equations are syntactic helper
premises; the flat run and postconditions are proved. -/
theorem evaluateDecs_noop_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (env : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (nextEnv : Environment) (flatDecs : List FlatLang.Exp) (decs : List Dec)
    (result : Result (SemEnv Value) Value)
    (sourceNoop : EvaluateHOL.evaluateDecs source sourceEnv decs =
      (source, .val (⟨nsEmpty, nsEmpty⟩ : SemEnv Value)))
    (compileNoop : compileDecs trace n start env gen decs = (n, start, emptyEnv, gen, []))
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv decs = (sourceLast, result))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs trace n start env gen decs = (n', next, nextEnv, nextGen, flatDecs))
    (generation : envGenRel gen source.evalState) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result := by
  have sourcePair := sourceRun.symm.trans sourceNoop
  have lastEq : sourceLast = source := congrArg Prod.fst sourcePair
  have resultEq : result = .val (⟨nsEmpty, nsEmpty⟩ : SemEnv Value) := congrArg Prod.snd sourcePair
  have compilePair := compiled.symm.trans compileNoop
  simp only [Prod.mk.injEq] at compilePair
  obtain ⟨_, nextEq, envEq, genEq, decsEq⟩ := compilePair
  subst sourceLast
  subst result
  subst next
  subst nextEnv
  subst nextGen
  subst flatDecs
  refine ⟨flat, genv, none, ?_, invariant.2.2.1, ?_, ?_, ?_⟩
  · simp [FlatSem.evaluateDecs]
  · intro _
    exact ⟨invariant, oracForwardRel_refl interp source.evalState, GlobalGrowth.refl genv⟩
  · intro resultEnv same
    cases same
    exact ⟨rfl, envDomainEq_empty, generation, globalEnvInv_empty genv⟩
  · intro error impossible
    cases impossible

/-- Empty declaration-list case over the factored compiler relations. -/
theorem evaluateDecs_empty_case {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [] = (sourceLast, result))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs trace n start env gen [] = (n', next, nextEnv, nextGen, flatDecs))
    (_envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (_notTypeError : result ≠ .err (.abort .typeError))
    (generation : envGenRel gen source.evalState)
    (_future : envGenFutureRel interp nextGen source.evalState)
    (_bounded : idxPrev next finish) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result := by
  apply evaluateDecs_noop_factored interp transform genv env sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen nextEnv flatDecs [] result
  · simp only [EvaluateHOL.evaluateDecs]
    rfl
  · simp [compileDecs]
  · exact sourceRun
  · exact invariant
  · exact compiled
  · exact generation

/-- Type-abbreviation declaration case over the factored compiler relations. -/
theorem evaluateDtabbrev_case {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (source sourceLast : State F) (flat : FlatSem.State C F) (start finish next : NextIndices)
    (other : Set (Nat × IndexKind)) (n n' : Nat) (gen nextGen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (typeVars : List TvarN) (name : TypeN) (typ : AstT)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dtabbrev location typeVars name typ] =
      (sourceLast, result))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs trace n start env gen [.dtabbrev location typeVars name typ] =
      (n', next, nextEnv, nextGen, flatDecs))
    (_envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (_notTypeError : result ≠ .err (.abort .typeError))
    (generation : envGenRel gen source.evalState)
    (_future : envGenFutureRel interp nextGen source.evalState)
    (_bounded : idxPrev next finish) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result := by
  apply evaluateDecs_noop_factored interp transform genv env sourceEnv trace source sourceLast flat
    start finish next other n n' gen nextGen nextEnv flatDecs [.dtabbrev location typeVars name typ] result
  · simp only [EvaluateHOL.evaluateDecs]
    rfl
  · simp [compileDecs]
  · exact sourceRun
  · exact invariant
  · exact compiled
  · exact generation

end Flapjack.Compiler.Backend.SourceToFlat
