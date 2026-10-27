import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleInvariant
import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Misc.Option

/-! Source-oracle decoding and incremental compiler steps. -/
namespace Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

private instance : Nonempty Config :=
  ⟨{ next := ⟨0, 0, 0⟩, modEnv := emptyEnv, patternCfg := ⟨0⟩, envs := ⟨0, .ln⟩ }⟩

/-- Allocated environment identifiers lie below the next generation counter. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_gen_inv_def"]
def envGenInv (gen : EnvironmentGenerationStore) : Prop :=
  ∀ i, Flapjack.sptMem i gen.envs → i < gen.next

/-- Allocated environment generations lie below the next counter. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_store_inv_def"]
def envStoreInv (store : EnvironmentStore) : Prop :=
  ∀ i, Flapjack.sptMem i store.envGens → i < store.next

/-- Current compiler and source-oracle generations agree. The bounded index
premise makes the optional lookup agree with HOL's `EL`. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_gen_rel_def"]
def envGenRel (gen : EnvironmentGenerationStore) (evalState : Option EvalState) : Prop :=
  match evalState with
  | none => True
  | some (.evalOracle state) =>
    gen.generation = state.generation ∧ state.generation < state.envs.length ∧
      gen.next = (state.envs[state.generation]?.getD []).length
  | _ => False

/-- The next source-oracle configuration retains the current generation's
previously allocated environment mappings. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_gen_future_rel_def"]
def envGenFutureRel {C : Type} (interp : Option (Value → Option (Config × C)))
    (gen : EnvironmentGenerationStore) (evalState : Option EvalState) : Prop :=
  match srcOracNextCfg interp evalState with
  | none => True
  | some config => ∃ genFinal,
    Flapjack.sptLookup gen.generation config.envs.envGens = some genFinal ∧
      Flapjack.sptSubspt gen.envs genFinal

/-- The source oracle is decodable at each step, and successive decoded
configurations agree with incremental compilation. HOL types are inhabited;
`Nonempty C` supplies the payload inhabitance needed for HOL's `THE NONE`. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "src_orac_step_invs_def"]
noncomputable def srcOracStepInvs {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (evalState : Option EvalState) : Prop :=
  match interp, evalState with
  | none, none => True
  | some decode, some (.evalOracle state) =>
    (∀ k envId stateValue decs, state.oracle k = (envId, stateValue, decs) →
      ∃ config payload, decode stateValue = some (config, payload)) ∧
    let configAt := fun k => (Flapjack.holThe (decode (state.oracle k).2.1)).1
    ∀ k envId stateValue decs, state.oracle k = (envId, stateValue, decs) →
      configAt (k + 1) = (incCompileProg envId (configAt k) (transform decs)).1
  | _, _ => False

/-- The first two source-oracle entries expose consecutive incremental
compilation configurations. This is the original local `step_1` statement. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "step_1"]
theorem sourceOracle_firstStep {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (state : EvalOracleState)
    (steps : srcOracStepInvs interp transform (some (.evalOracle state))) :
    ∃ decode envId0 value0 decs0 flatDecs config0 payload0 envId1 value1 decs1 config1 payload1,
      interp = some decode ∧
      state.oracle 0 = (envId0, value0, decs0) ∧
      state.oracle 1 = (envId1, value1, decs1) ∧
      decode value0 = some (config0, payload0) ∧
      decode value1 = some (config1, payload1) ∧
      incCompileProg envId0 config0 (transform decs0) = (config1, flatDecs) ∧
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some config0 := by
  cases interp with
  | none => simp [srcOracStepInvs] at steps
  | some decode =>
    simp only [srcOracStepInvs] at steps
    cases firstEntry : state.oracle 0 with
    | mk envId0 tail0 =>
      cases tail0 with
      | mk value0 decs0 =>
        cases secondEntry : state.oracle 1 with
        | mk envId1 tail1 =>
          cases tail1 with
          | mk value1 decs1 =>
            obtain ⟨config0, payload0, decoded0⟩ := steps.1 0 envId0 value0 decs0 firstEntry
            obtain ⟨config1, payload1, decoded1⟩ := steps.1 1 envId1 value1 decs1 secondEntry
            have advance := steps.2 0 envId0 value0 decs0 firstEntry
            simp only [Nat.zero_add, firstEntry, secondEntry, decoded0, decoded1, Flapjack.holThe] at advance
            refine ⟨decode, envId0, value0, decs0, (incCompileProg envId0 config0 (transform decs0)).2,
              config0, payload0, envId1, value1, decs1, config1, payload1,
              rfl, rfl, rfl, decoded0, decoded1, ?_, ?_⟩
            · exact Prod.ext advance.symm rfl
            · simp [srcOracNextCfg, srcOracNextCfgInner, firstEntry, decoded0]

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
