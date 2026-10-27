import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleInvariant
import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.FiniteMapGrowth
import Flapjack.Misc.Option
import Flapjack.Misc.Sptree.Subspt
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

/-- Compiling declarations does not change their environment generation. -/
theorem compileDecs_generation_core (t : List Flapjack.Basis.Pure.MlString.MlString)
    (n : Nat) (next : NextIndices) (env : Environment) (envs : EnvironmentGenerationStore)
    (decs : List Dec) : (compileDecs t n next env envs decs).2.2.2.1.generation = envs.generation := by
  fun_induction compileDecs t n next env envs decs <;> simp_all

/-- Compilation preserves the environment generation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_decs_generation"]
theorem compileDecs_generation (t : List Flapjack.Basis.Pure.MlString.MlString)
    (n : Nat) (next : NextIndices) (env : Environment) (envs : EnvironmentGenerationStore)
    (decs : List Dec) (n' : Nat) (next' : NextIndices) (env' : Environment)
    (envs' : EnvironmentGenerationStore) (flatDecs : List FlatLang.Exp)
    (compiled : compileDecs t n next env envs decs = (n', next', env', envs', flatDecs)) :
    envs'.generation = envs.generation := by
  simpa [compiled] using compileDecs_generation_core t n next env envs decs

/-- Declaration compilation advances or preserves each allocation counter. -/
theorem compileDecs_idxPrev_core (t : List Flapjack.Basis.Pure.MlString.MlString)
    (n : Nat) (next : NextIndices) (env : Environment) (envs : EnvironmentGenerationStore)
    (decs : List Dec) : idxPrev next (compileDecs t n next env envs decs).2.1 := by
  fun_induction compileDecs t n next env envs decs <;> simp_all [idxPrev] <;> omega

/-- The declaration compiler's output indices are at least its input indices. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_decs_idx_prev"]
theorem compileDecs_idxPrev (t : List Flapjack.Basis.Pure.MlString.MlString)
    (n : Nat) (next : NextIndices) (env : Environment) (envs : EnvironmentGenerationStore)
    (decs : List Dec) (n' : Nat) (next' : NextIndices) (env' : Environment)
    (envs' : EnvironmentGenerationStore) (flatDecs : List FlatLang.Exp)
    (compiled : compileDecs t n next env envs decs = (n', next', env', envs', flatDecs)) :
    idxPrev next next' := by
  simpa [compiled] using compileDecs_idxPrev_core t n next env envs decs

/-- Compiling declarations preserves allocation bounds and previously stored
environment mappings. -/
private theorem freshGenerationInsert (env : Environment) (envs : EnvironmentGenerationStore)
    (valid : envGenInv envs) :
    envGenInv { envs with next := envs.next + 1, envs := Flapjack.sptInsert envs.next env envs.envs } ∧
      Flapjack.sptSubspt envs.envs (Flapjack.sptInsert envs.next env envs.envs) := by
  constructor
  · intro i mem
    change i < envs.next + 1
    rw [Flapjack.sptMem_sptInsert] at mem
    rcases mem with eq | old
    · omega
    · have := valid i old; omega
  · intro i mem
    have bound := valid i mem
    have ne : i ≠ envs.next := by omega
    exact ⟨(Flapjack.sptMem_sptInsert _ _ _ _).2 (Or.inr mem),
      Flapjack.sptLookup_sptInsert_ne _ _ _ _ ne⟩

theorem compileDecs_envGenInv_core (t : List Flapjack.Basis.Pure.MlString.MlString)
    (n : Nat) (next : NextIndices) (env : Environment) (envs : EnvironmentGenerationStore)
    (decs : List Dec) :
    envGenInv envs →
      envGenInv (compileDecs t n next env envs decs).2.2.2.1 ∧
      Flapjack.sptSubspt envs.envs (compileDecs t n next env envs decs).2.2.2.1.envs := by
  fun_induction compileDecs t n next env envs decs <;>
    simp_all [Flapjack.sptSubspt, freshGenerationInsert]
  intro valid
  exact (freshGenerationInsert _ _ valid).2

/-- Declaration compilation preserves generation-store validity and its
existing mappings. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_decs_env_gen_inv"]
theorem compileDecs_envGenInv (t : List Flapjack.Basis.Pure.MlString.MlString)
    (n : Nat) (next : NextIndices) (env : Environment) (envs : EnvironmentGenerationStore)
    (decs : List Dec) (n' : Nat) (next' : NextIndices) (env' : Environment)
    (envs' : EnvironmentGenerationStore) (flatDecs : List FlatLang.Exp)
    (compiled : compileDecs t n next env envs decs = (n', next', env', envs', flatDecs))
    (valid : envGenInv envs) : envGenInv envs' ∧ Flapjack.sptSubspt envs.envs envs'.envs := by
  simpa [compiled] using compileDecs_envGenInv_core t n next env envs decs valid

/-- Incremental compilation adds a fresh environment generation and retains
every previously stored generation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "inc_compile_prog_env_submap"]
theorem incCompileProg_envSubmap (envId : Nat × Nat) (config next : Config)
    (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (compiled : incCompileProg envId config decs = (next, flatDecs))
    (valid : envStoreInv config.envs) :
    envStoreInv next.envs ∧ Flapjack.sptSubspt config.envs.envGens next.envs.envGens := by
  generalize resultEq : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs = result at compiled
  rcases result with ⟨n, indices, env, gen, compiledDecs⟩
  simp only [incCompileProg, resultEq] at compiled
  have nextEq : next = { config with next := indices, envs :=
      ⟨config.envs.next + 1,
        Flapjack.sptInsert config.envs.next (Flapjack.sptInsert gen.next (extendEnv env (lookupEnvId envId config.envs)) gen.envs) config.envs.envGens⟩ } :=
    (Prod.mk.inj compiled).1.symm
  subst next
  dsimp only
  constructor
  · intro i mem
    change i < config.envs.next + 1
    rw [Flapjack.sptMem_sptInsert] at mem
    rcases mem with eq | old
    · omega
    · have := valid i old; omega
  · intro i mem
    have bound := valid i mem
    have ne : i ≠ config.envs.next := by omega
    constructor
    · exact (Flapjack.sptMem_sptInsert _ _ _ _).2 (Or.inr mem)
    · exact Flapjack.sptLookup_sptInsert_ne _ _ _ _ ne

/-- Incremental compilation advances the environment generation by one. -/
theorem incCompileProg_envNext (envId : Nat × Nat) (config : Config) (decs : List Dec) :
    (incCompileProg envId config decs).1.envs.next = config.envs.next + 1 := by
  generalize h : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs = result
  rcases result with ⟨n, indices, env, gen, compiledDecs⟩
  simp [incCompileProg, h]

/-- Incremental compilation advances or preserves each allocation counter. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "inc_compile_prog_idx_prev"]
theorem incCompileProg_idxPrev (envId : Nat × Nat) (config next : Config)
    (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (compiled : incCompileProg envId config decs = (next, flatDecs)) :
    idxPrev config.next next.next := by
  generalize h : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs = result at compiled
  rcases result with ⟨n, indices, env, gen, compiledDecs⟩
  have indicesPrev := compileDecs_idxPrev [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs n indices env gen compiledDecs h
  simp only [incCompileProg, h] at compiled
  have nextEq := (Prod.mk.inj compiled).1
  simpa [← nextEq] using indicesPrev

/-- The generation produced while compiling incremental declarations is
stored in the resulting configuration, with all of its existing mappings. -/
theorem incCompileProg_envGenFuture (envId : Nat × Nat) (config : Config) (decs : List Dec) :
    let gen := (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs).2.2.2.1
    ∃ final, Flapjack.sptLookup gen.generation (incCompileProg envId config decs).1.envs.envGens = some final ∧
      Flapjack.sptSubspt gen.envs final := by
  generalize h : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs = result
  rcases result with ⟨n, indices, env, gen, flatDecs⟩
  have generation : gen.generation = config.envs.next := by
    simpa [h] using compileDecs_generation_core [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs
  have valid : envGenInv gen := by
    have initial : envGenInv (⟨0, config.envs.next, .ln⟩ : EnvironmentGenerationStore) := by
      simp [envGenInv]
    have inv := compileDecs_envGenInv_core [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs initial
    simpa [h] using inv.1
  refine ⟨Flapjack.sptInsert gen.next (extendEnv env (lookupEnvId envId config.envs)) gen.envs, ?_, ?_⟩
  · simp [incCompileProg, h, generation, Flapjack.sptLookup_sptInsert_same]
  · exact (freshGenerationInsert _ _ valid).2

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

/-- An Eval step advances to the compiler's next configuration while
preserving the old environment-generation map. The source environment
invariant supplies the initial store bound needed by the original submap
theorem; full preservation of the environment invariant remains separate. -/
theorem sourceOracle_envStoreAdvance {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (state : EvalOracleState)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (envs : srcOracEnvInvs (some decode) genv (some (.evalOracle state))) :
    ∃ current next,
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some current ∧
      srcOracNextCfg (some decode)
        (some (.evalOracle (addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }))) = some next ∧
      current.envs.next = state.envs.length ∧ next.envs.next = current.envs.next + 1 ∧ envStoreInv next.envs ∧
      Flapjack.sptSubspt current.envs.envGens next.envs.envGens := by
  obtain ⟨_, envId, value, decs, flatDecs, current, payload, nextId, nextValue, nextDecs,
    next, nextPayload, decoderEq, entry, nextEntry, decoded, nextDecoded, compiled, currentCfg⟩ :=
    sourceOracle_firstStep (some decode) transform state steps
  cases decoderEq
  obtain ⟨stored, storedCfg, valid, length, _⟩ := envs
  rw [currentCfg] at storedCfg
  cases storedCfg
  obtain ⟨nextValid, submap⟩ := incCompileProg_envSubmap envId current next (transform decs) flatDecs compiled valid
  have nextLength := incCompileProg_envNext envId current (transform decs)
  rw [compiled] at nextLength
  refine ⟨current, next, currentCfg, ?_, length, nextLength, nextValid, submap⟩
  simp [srcOracNextCfg, srcOracNextCfgInner, addEnvGeneration, Flapjack.holShiftSeq, nextEntry, nextDecoded]

/-- Advancing an oracle preserves the stored source-environment invariant.
Existing generations keep their compiler maps; the newly appended generation
is empty. This uses the factored `GlobalEnvInv` relation. -/
theorem srcOracEnvInvs_advance {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (state : EvalOracleState)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (invs : srcOracEnvInvs (some decode) genv (some (.evalOracle state))) :
    srcOracEnvInvs (some decode) genv
      (some (.evalOracle (addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }))) := by
  obtain ⟨current, next, currentCfg, nextCfg, length, nextLength, valid, submap⟩ :=
    sourceOracle_envStoreAdvance decode transform genv state steps invs
  obtain ⟨old, oldCfg, _, _, oldEnvs⟩ := invs
  rw [currentCfg] at oldCfg
  cases oldCfg
  refine ⟨next, nextCfg, valid, ?_, ?_⟩
  · simpa [addEnvGeneration, length] using nextLength
  · intro gId gBound id idBound
    by_cases oldBound : gId < state.envs.length
    · have oldIdBound : id < state.envs[gId].length := by
        simpa [addEnvGeneration, List.getElem_append_left, oldBound] using idBound
      obtain ⟨mapGen, compMap, generation, mapping, inv⟩ := oldEnvs gId oldBound id oldIdBound
      have mem : Flapjack.sptMem gId current.envs.envGens :=
        Flapjack.sptMem_iff_lookup _ _ |>.2 ⟨mapGen, generation⟩
      have nextLookup := (submap gId mem).2
      refine ⟨mapGen, compMap, ?_, mapping, ?_⟩
      · exact nextLookup.trans generation
      · simpa [addEnvGeneration, List.getElem_append_left, oldBound] using inv
    · have bound : gId < state.envs.length + 1 := by simpa [addEnvGeneration] using gBound
      have eq : gId = state.envs.length := by omega
      subst gId
      simp [addEnvGeneration] at idBound

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
