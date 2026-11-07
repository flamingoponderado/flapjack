import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation
import Flapjack.SemanticPrimitivesHOL.EvalState
import Lean.Elab.Tactic.Omega

/-! Source declaration-environment recording simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

/-- Flapjack proof infrastructure: appending an environment preserves recorded lookups. -/
private theorem declareForward (oracle : EvalOracleState) (env : SemEnv Value)
    (valid : oracle.generation < oracle.envs.length) :
    let generation := oracle.envs[oracle.generation]
    let updated := { oracle with envs := oracle.envs.set oracle.generation (generation ++ [env]) }
    envStoreForward oracle updated := by
  dsimp only
  refine ⟨by simp, ?_⟩
  intro id result found
  rcases id with ⟨g, i⟩
  simp only [lookupEnv] at found ⊢
  by_cases same : g = oracle.generation
  · subst g
    have prior : oracle.envs[oracle.generation][i]? = some result := by
      simpa [List.getElem?_eq_getElem valid] using found
    have bound : i < oracle.envs[oracle.generation].length := by
      by_contra no
      simp [List.getElem?_eq_none (by omega : oracle.envs[oracle.generation].length ≤ i)] at prior
    simpa [valid, List.getElem?_append, bound] using prior
  · simpa [Ne.symm same] using found

/-- Flapjack proof infrastructure: the appended environment is available at its new index. -/
private theorem declareLookup (oracle : EvalOracleState) (env : SemEnv Value)
    (valid : oracle.generation < oracle.envs.length) :
    let generation := oracle.envs[oracle.generation]
    let updated := { oracle with envs := oracle.envs.set oracle.generation (generation ++ [env]) }
    lookupEnv updated (oracle.generation, generation.length) = some env := by
  dsimp only
  simp [lookupEnv, valid]

/-- Flapjack proof infrastructure: updating the current generation preserves its prefix. -/
private theorem declareStack (oracle : EvalOracleState) (env : SemEnv Value)
    (valid : oracle.generation < oracle.envs.length) :
    let generation := oracle.envs[oracle.generation]
    let updated := { oracle with envs := oracle.envs.set oracle.generation (generation ++ [env]) }
    envStackForward oracle updated := by
  dsimp only
  constructor
  · rfl
  · intro j bound
    simp [Flapjack.holEl_set, valid, Nat.ne_of_gt bound]

/-- Declaration recording advances related states and preserves the generation stack. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "declare_env_sim"]
theorem declareEnv_sim {Config F : Type} (s : State F) (env : SemEnv Value)
    (v : Value) (es : Option EvalState) (ci : CompilerInstance Config)
    (t : State F) (env' : SemEnv Value)
    (premises : declareEnv s.evalState env = some (v, es) ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env') :
    ∃ v' es₂, envStoreForward (oracleState t.evalState) (oracleState es₂) ∧
      declareEnv t.evalState env' = some (v', es₂) ∧
      ValueRel (oracleState es₂) v v' ∧
      stateRel ci { s with evalState := es } { t with evalState := es₂ } ∧
      envStackForward (oracleState t.evalState) (oracleState es₂) := by
  obtain ⟨declared, ⟨dec, oracle, refs, target, stores, sourceEval, callback,
    compilerState, decoder, compiler, initial, oracleInitial, counter, valid, wf⟩, envRelated⟩ := premises
  subst t
  simp only [oracleState] at envRelated ⊢
  rw [sourceEval] at declared
  simp only [declareEnv] at declared
  rcases dec with ⟨comp, config, ids, decode⟩
  rcases ids with ⟨generation, nextId, nextGeneration⟩
  simp only at declared counter
  cases declared
  cases counter
  let generationEnv := oracle.envs[oracle.generation]
  let updated := { oracle with envs := oracle.envs.set oracle.generation (generationEnv ++ [env']) }
  have forward : envStoreForward oracle updated := declareForward oracle env' valid
  have lookup : lookupEnv updated (oracle.generation, generationEnv.length) = some env' :=
    declareLookup oracle env' valid
  have stack : envStackForward oracle updated := declareStack oracle env' valid
  refine ⟨.conv none [natToValue oracle.generation, natToValue generationEnv.length],
    some (.evalOracle updated), ?_, ?_, ?_, ?_, ?_⟩
  · exact forward
  · simp [declareEnv, valid, updated, generationEnv]
  · apply ValueRel.env
    · simp [valueToEnvId, valueToNat, natToValue, generationEnv, Flapjack.holEl_eq_getElem _ _ valid]
    · simpa [generationEnv, Flapjack.holEl_eq_getElem _ _ valid] using lookup
    · apply (valueEnvRel_iff _ _ _).mpr
      exact (forwardRules oracle (.conv none []) (.conv none []) updated [] [] env env').2.2.1 ⟨envRelated, forward⟩
  · refine ⟨⟨comp, config, (oracle.generation, (Flapjack.holEl oracle.generation oracle.envs).length + 1,
        oracle.envs.length), decode⟩, updated, refs, rfl, ?_⟩
    refine ⟨(forwardRules oracle (.conv none []) (.conv none []) updated [] [] env env').2.2.2 _ _ ⟨stores, forward⟩, rfl, ?_⟩
    simp only [updated]
    refine ⟨callback, compilerState, decoder, compiler, initial, oracleInitial, ?_, ?_, wf⟩
    · simp [Flapjack.holEl_set, valid, generationEnv, Flapjack.holEl_eq_getElem _ _ valid]
    · simpa using valid
  · exact stack


end Flapjack.Compiler.Backend.SourceEval.Proofs
