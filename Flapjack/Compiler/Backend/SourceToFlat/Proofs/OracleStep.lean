import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleInvariant
import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.FiniteMapGrowth
import Flapjack.Misc.Option
import Flapjack.HolArb
import Flapjack.SemanticPrimitivesHOL.EvalState

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

/-- The oracle generation is valid. HOL's incomplete `EvalDecs` case is the
fixed unspecified Boolean `ARB`, not a chosen false value. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "src_orac_gen_inv_def"]
noncomputable def srcOracGenInv (evalState : Option EvalState) : Prop :=
  match evalState with
  | none => True
  | some (.evalOracle state) => state.generation < state.envs.length
  | some (.evalDecs _) => Flapjack.holArb Bool = true

/-- Every stored source oracle environment has a related compiler map. This
uses Flapjack's factored global environment relation, whose HOL correspondence
is still under review, and therefore is not tagged as the original invariant. -/
def srcOracEnvInvs {C : Type} (interp : Option (Value → Option (Config × C)))
    (genv : GlobalEnv) (evalState : Option EvalState) : Prop :=
  match evalState with
  | none => True
  | some (.evalDecs _) => False
  | some (.evalOracle state) =>
    ∃ config, srcOracNextCfg interp evalState = some config ∧ envStoreInv config.envs ∧
      config.envs.next = state.envs.length ∧
      ∀ gId (gBound : gId < state.envs.length) id (idBound : id < state.envs[gId].length),
        ∃ mapGen compMap, Flapjack.sptLookup gId config.envs.envGens = some mapGen ∧
          Flapjack.sptLookup id mapGen = some compMap ∧
          GlobalEnvInv genv compMap (fun _ => False) state.envs[gId][id]

/-- Stored source-oracle environment relationships survive global growth. -/
theorem srcOracEnvInvs_growth {C : Type} (interp : Option (Value → Option (Config × C)))
    (old new : GlobalEnv) (growth : GlobalGrowth old new) (evalState : Option EvalState)
    (invs : srcOracEnvInvs interp old evalState) : srcOracEnvInvs interp new evalState := by
  cases evalState with
  | none => trivial
  | some state =>
    cases state with
    | evalDecs state => exact invs
    | evalOracle state =>
      obtain ⟨config, next, store, length, envs⟩ := invs
      refine ⟨config, next, store, length, ?_⟩
      intro gId gBound id idBound
      obtain ⟨mapGen, compMap, generationLookup, mapLookup, inv⟩ := envs gId gBound id idBound
      exact ⟨mapGen, compMap, generationLookup, mapLookup,
        globalEnvInv_growth old new growth compMap (fun _ => False) _ inv⟩

/-- A source oracle environment lookup finds the corresponding stored compiler
map and global invariant. This uses the factored relation and is not yet a
reviewed port of the original HOL lookup theorem. -/
theorem srcOracEnvInvs_lookup {C : Type} (interp : Option (Value → Option (Config × C)))
    (genv : GlobalEnv) (state : EvalOracleState) (envId : Nat × Nat)
    (sourceEnv : SemEnv Value) (stateValue : Value) (decs : List Dec)
    (lookup : lookupEnv state envId = some sourceEnv)
    (invs : srcOracEnvInvs interp genv (some (.evalOracle state)))
    (entry : state.oracle 0 = (envId, stateValue, decs)) :
    ∃ decode config payload mapGen compMap,
      interp = some decode ∧ decode stateValue = some (config, payload) ∧
      Flapjack.sptLookup envId.1 config.envs.envGens = some mapGen ∧
      Flapjack.sptLookup envId.2 mapGen = some compMap ∧
      GlobalEnvInv genv compMap (fun _ => False) sourceEnv := by
  obtain ⟨config, next, _, _, envs⟩ := invs
  cases generation : state.envs[envId.1]? with
  | none => simp [lookupEnv, generation] at lookup
  | some stored =>
    have found : stored[envId.2]? = some sourceEnv := by simpa [lookupEnv, generation] using lookup
    obtain ⟨gBound, gEq⟩ := List.getElem?_eq_some_iff.mp generation
    obtain ⟨idBound, idEq⟩ := List.getElem?_eq_some_iff.mp found
    have idBound' : envId.2 < state.envs[envId.1].length := by simpa [gEq] using idBound
    obtain ⟨mapGen, compMap, generationLookup, mapLookup, inv⟩ :=
      envs envId.1 gBound envId.2 idBound'
    have inv' : GlobalEnvInv genv compMap (fun _ => False) sourceEnv := by
      simpa [gEq, idEq] using inv
    cases interp with
    | none => simp [srcOracNextCfg, srcOracNextCfgInner] at next
    | some decode =>
      cases decoded : decode stateValue with
      | none => simp [srcOracNextCfg, srcOracNextCfgInner, entry, decoded] at next
      | some result =>
        rcases result with ⟨decodedConfig, payload⟩
        simp [srcOracNextCfg, srcOracNextCfgInner, entry, decoded] at next
        subst decodedConfig
        exact ⟨decode, config, payload, mapGen, compMap, rfl, decoded, generationLookup, mapLookup, inv'⟩

/-- The actual compiler environment lookup returns the map supplied by the
source-oracle invariant. -/
theorem srcOracEnvInvs_lookupEnvId {C : Type} (interp : Option (Value → Option (Config × C)))
    (genv : GlobalEnv) (state : EvalOracleState) (envId : Nat × Nat)
    (sourceEnv : SemEnv Value) (stateValue : Value) (decs : List Dec)
    (lookup : lookupEnv state envId = some sourceEnv)
    (invs : srcOracEnvInvs interp genv (some (.evalOracle state)))
    (entry : state.oracle 0 = (envId, stateValue, decs)) :
    ∃ decode config payload,
      interp = some decode ∧ decode stateValue = some (config, payload) ∧
      GlobalEnvInv genv (lookupEnvId envId config.envs) (fun _ => False) sourceEnv := by
  obtain ⟨decode, config, payload, mapGen, compMap, chosen, decoded, generation, mapping, inv⟩ :=
    srcOracEnvInvs_lookup interp genv state envId sourceEnv stateValue decs lookup invs entry
  refine ⟨decode, config, payload, chosen, decoded, ?_⟩
  simpa [lookupEnvId, generation, mapping] using inv

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

/-- Combined source-oracle conditions using the factored environment
relation. This is not yet the original HOL invariant. -/
noncomputable def srcOracInvs {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (evalState : Option EvalState) : Prop :=
  srcOracStepInvs interp transform evalState ∧ srcOracEnvInvs interp genv evalState ∧
    srcOracGenInv evalState

/-- The factored source-oracle invariant is stable under the original
subglobal and submap growth hypotheses. -/
theorem srcOracInvs_growth {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (old new : GlobalEnv) (evalState : Option EvalState)
    (premises : srcOracInvs interp transform old evalState ∧ finiteSubmap old.c new.c ∧
      finiteSubmap old.tys new.tys ∧ subglobals old.v new.v) :
    srcOracInvs interp transform new evalState := by
  obtain ⟨⟨steps, envs, gen⟩, constructors, types, slots⟩ := premises
  have growth := GlobalGrowth.ofSubmaps old new slots constructors types
  exact ⟨steps, srcOracEnvInvs_growth interp old new growth evalState envs, gen⟩

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

/-- An oracle environment lookup and the first incremental step agree on the
same compiler configuration and its stored global environment. This is
infrastructure over the factored global environment relation. -/
theorem sourceOracle_lookup_firstStep {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (state : EvalOracleState) (envId : Nat × Nat)
    (sourceEnv : SemEnv Value) (stateValue : Value) (decs : List Dec)
    (lookup : lookupEnv state envId = some sourceEnv)
    (invs : srcOracInvs interp transform genv (some (.evalOracle state)))
    (entry : state.oracle 0 = (envId, stateValue, decs)) :
    ∃ decode config payload nextId nextValue nextDecs nextConfig nextPayload flatDecs,
      interp = some decode ∧ decode stateValue = some (config, payload) ∧
      GlobalEnvInv genv (lookupEnvId envId config.envs) (fun _ => False) sourceEnv ∧
      state.oracle 1 = (nextId, nextValue, nextDecs) ∧
      decode nextValue = some (nextConfig, nextPayload) ∧
      incCompileProg envId config (transform decs) = (nextConfig, flatDecs) ∧
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some config := by
  obtain ⟨decode, config, payload, chosen, decoded, globalInv⟩ :=
    srcOracEnvInvs_lookupEnvId interp genv state envId sourceEnv stateValue decs lookup invs.2.1 entry
  have steps := invs.1
  rw [chosen] at steps
  simp only [srcOracStepInvs] at steps
  cases nextEntry : state.oracle 1 with
  | mk nextId tail =>
    cases tail with
    | mk nextValue nextDecs =>
      obtain ⟨nextConfig, nextPayload, nextDecoded⟩ := steps.1 1 nextId nextValue nextDecs nextEntry
      have advance := steps.2 0 envId stateValue decs entry
      simp only [Nat.zero_add, entry, nextEntry, decoded, nextDecoded, Flapjack.holThe] at advance
      refine ⟨decode, config, payload, nextId, nextValue, nextDecs, nextConfig, nextPayload,
        (incCompileProg envId config (transform decs)).2, chosen, decoded, globalInv, rfl,
        nextDecoded, Prod.ext advance.symm rfl, ?_⟩
      simp [srcOracNextCfg, srcOracNextCfgInner, entry, decoded]

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
