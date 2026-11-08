import Flapjack.NamespaceProps.Append
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalDeclarations

/-! Namespace-domain facts needed by sequential declaration simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Updating the value namespace retains the constructor namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "sem_env_eq_lemma"]
theorem semEnv_update_values {α β : Type} : ∀ (env : SemEnv α) (x : Namespace ModN VarN β),
    { env with v := x } = ⟨x, env.c⟩ := by
  intro env x
  cases env
  rfl

/-- Extending compiler and source environments preserves their value,
constructor, and module domains. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_domain_eq_append"]
theorem envDomainEq_append (first second : Environment) (sourceFirst sourceSecond : SemEnv Value)
    (premises : EnvDomainEq first sourceFirst ∧ EnvDomainEq second sourceSecond) :
    EnvDomainEq (extendEnv first second) (extendDecEnv sourceFirst sourceSecond) := by
  obtain ⟨⟨v1, vm1, c1, cm1⟩, ⟨v2, vm2, c2, cm2⟩⟩ := premises
  have values := nsDom_nsAppend_equal first.v second.v sourceFirst.v sourceSecond.v ⟨v1, v2, vm1, vm2⟩
  have constructors := nsDom_nsAppend_equal first.c second.c sourceFirst.c sourceSecond.c ⟨c1, c2, cm1, cm2⟩
  exact ⟨values.1, values.2, constructors.1, constructors.2⟩

namespace GlobalEnvAppendPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end GlobalEnvAppendPort

/-- Extending the value namespace with compiler bindings preserves the global
environment invariant when their domain matches the new source namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "global_env_inv_extend2"
  (fmap_as_finite_support := [c, tys])]
theorem globalEnvInv_extendBindings (genv : GlobalEnv) (compMap : Environment)
    (env : SemEnv Value) (newVars : List (VarN × VarName))
    (env' : Namespace ModN VarN Value) (locals : VarN → Prop)
    (envC : Namespace ModN ConN (Nat × Stamp))
    (premises : (fun id => id ∈ newVars.map (fun p => Ident.short p.1)) = nsDom env' ∧
      GlobalEnvInv genv compMap locals env ∧
      GlobalEnvInv genv { compMap with v := alistToNs newVars } locals ⟨env', envC⟩) :
    GlobalEnvInv genv { compMap with v := nsBindList newVars compMap.v } locals
      { env with v := nsAppend env' env.v } := by
  obtain ⟨domain, base, added⟩ := premises
  obtain ⟨baseValues, baseConstructors⟩ := (globalEnvInv_iff genv compMap locals env).mp base
  obtain ⟨addedValues, _⟩ := (globalEnvInv_iff genv { compMap with v := alistToNs newVars }
    locals ⟨env', envC⟩).mp added
  apply (globalEnvInv_iff _ _ _ _).mpr
  constructor
  · intro id value notShadowed sourceLookup
    cases id with
    | short name =>
      rw [nsLookup_append_short] at sourceLookup
      cases first : nsLookup env' (.short name) with
      | some firstValue =>
        simp [first] at sourceLookup
        subst firstValue
        obtain ⟨n, flat, t, lookup, bound, slot, related⟩ := addedValues (.short name) value notShadowed first
        refine ⟨n, flat, t, ?_, bound, slot, related⟩
        rw [← nsAppend_to_nsBindList, nsLookup_append_short]
        simp [lookup]
      | none =>
        have noBinding : nsLookup (alistToNs newVars : Namespace ModN VarN VarName) (.short name) = none := by
          have atName := congrFun domain (.short name)
          simp only [nsDom] at atName
          cases found : nsLookup (alistToNs newVars : Namespace ModN VarN VarName) (.short name) with
          | none => rfl
          | some entry =>
            have member : (.short name : Ident ModN VarN) ∈ newVars.map (fun p => Ident.short p.1) := by
              have keyMember : name ∈ newVars.map Prod.fst := by
                have someLookup : (newVars.lookup name).isSome = true := by
                  simpa [alistToNs, nsLookup] using congrArg Option.isSome found
                obtain ⟨pair, member, key⟩ := List.lookup_isSome_iff.mp someLookup
                have keyEq : name = pair.1 := by simpa using key
                exact List.mem_map.mpr ⟨pair, member, keyEq.symm⟩
              simpa [List.mem_map] using keyMember
            have : ∃ v, nsLookup env' (.short name) = some v := by rw [← atName]; exact member
            simp [first] at this
        have source : nsLookup env.v (.short name) = some value := by simpa [first] using sourceLookup
        obtain ⟨n, flat, t, lookup, bound, slot, related⟩ := baseValues (.short name) value notShadowed source
        refine ⟨n, flat, t, ?_, bound, slot, related⟩
        rw [← nsAppend_to_nsBindList, nsLookup_append_short]
        simpa [noBinding] using lookup
    | long mod rest =>
      have firstNone : nsLookup env' (.long mod rest) = none := by
        have atName := congrFun domain (.long mod rest)
        simp only [nsDom] at atName
        cases found : nsLookup env' (.long mod rest) with
        | none => rfl
        | some v =>
          have : (.long mod rest : Ident ModN VarN) ∈ newVars.map (fun p => Ident.short p.1) := by
            rw [atName]; exact ⟨v, found⟩
          simp at this
      rw [nsLookup_append_long] at sourceLookup
      cases moduleLookup : nsLookupMod env' [mod] with
      | some module => simp [moduleLookup, firstNone] at sourceLookup
      | none =>
        have source : nsLookup env.v (.long mod rest) = some value := by simpa [moduleLookup] using sourceLookup
        obtain ⟨n, flat, t, lookup, bound, slot, related⟩ := baseValues (.long mod rest) value notShadowed source
        refine ⟨n, flat, t, ?_, bound, slot, related⟩
        rw [← nsAppend_to_nsBindList, nsLookup_append_long]
        simpa [alistToNs, nsLookupMod] using lookup
  · exact baseConstructors

/-- The global environment invariant composes across declaration extensions. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "global_env_inv_append"
  (fmap_as_finite_support := [c, tys])]
theorem globalEnvInv_append_factored (genv : GlobalEnv)
    (first second : Environment) (sourceFirst sourceSecond : SemEnv Value)
    (premises : EnvDomainEq first sourceFirst ∧
      GlobalEnvInv genv first (fun _ => False) sourceFirst ∧
      GlobalEnvInv genv second (fun _ => False) sourceSecond) :
    GlobalEnvInv genv (extendEnv first second) (fun _ => False)
      (extendDecEnv sourceFirst sourceSecond) := by
  obtain ⟨domain, firstInv, secondInv⟩ := premises
  obtain ⟨values1, constructors1⟩ := (globalEnvInv_iff genv first (fun _ => False) sourceFirst).mp firstInv
  obtain ⟨values2, constructors2⟩ := (globalEnvInv_iff genv second (fun _ => False) sourceSecond).mp secondInv
  obtain ⟨valueDomain, valueModules, constructorDomain, constructorModules⟩ := domain
  apply GlobalEnvInv.intro
  · intro id value _ sourceLookup
    let valueRelation : Value → VarName → Prop := fun v name =>
      ∃ n flat trace, name = .glob trace n ∧ n < genv.v.length ∧
        genv.v[n]?.getD none = some flat ∧ ValueRel genv v flat
    have left : ∀ v, nsLookup sourceFirst.v id = some v →
        ∃ name, nsLookup first.v id = some name ∧ valueRelation v name := by
      intro v lookup
      obtain ⟨n, flat, trace, target, bound, slot, related⟩ := values1 id v (by simp) lookup
      exact ⟨.glob trace n, target, n, flat, trace, rfl, bound, slot, related⟩
    have right : ∀ v, nsLookup sourceSecond.v id = some v →
        ∃ name, nsLookup second.v id = some name ∧ valueRelation v name := by
      intro v lookup
      obtain ⟨n, flat, trace, target, bound, slot, related⟩ := values2 id v (by simp) lookup
      exact ⟨.glob trace n, target, n, flat, trace, rfl, bound, slot, related⟩
    obtain ⟨name, lookup, n, flat, trace, nameEq, bound, slot, related⟩ :=
      nsLookup_append_transfer first.v second.v sourceFirst.v sourceSecond.v
        valueDomain valueModules id value valueRelation left right sourceLookup
    subst name
    exact .intro _ _ _ _ n flat trace lookup bound slot related
  · intro id arity stamp sourceLookup
    let constructorRelation : (Nat × Stamp) → (Nat × Option (Nat × List (Nat × Nat))) → Prop :=
      fun source target => genv.c.lookup ((target.1, target.2.map Prod.fst), source.1) = some source.2 ∧
        ∀ tyId ctors, target.2 = some (tyId, ctors) → genv.tys.lookup tyId = some ctors
    have left : ∀ v, nsLookup sourceFirst.c id = some v →
        ∃ c, nsLookup first.c id = some c ∧ constructorRelation v c := by
      rintro ⟨arity, stamp⟩ lookup
      obtain ⟨cn, group, target, mapped, types⟩ := constructors1 id arity stamp lookup
      exact ⟨(cn, group), target, mapped, types⟩
    have right : ∀ v, nsLookup sourceSecond.c id = some v →
        ∃ c, nsLookup second.c id = some c ∧ constructorRelation v c := by
      rintro ⟨arity, stamp⟩ lookup
      obtain ⟨cn, group, target, mapped, types⟩ := constructors2 id arity stamp lookup
      exact ⟨(cn, group), target, mapped, types⟩
    obtain ⟨⟨cn, group⟩, lookup, mapped, types⟩ :=
      nsLookup_append_transfer first.c second.c sourceFirst.c sourceSecond.c
        constructorDomain constructorModules id (arity, stamp) constructorRelation left right sourceLookup
    exact ⟨cn, group, lookup, mapped, types⟩

/-- Incremental compilation stores the extended compiler environment at the
next ID in the generation produced by compiling its declarations. -/
theorem incCompileProg_declaredEnvMap (envId : Nat × Nat) (config : Config) (decs : List Dec) :
    let initial := lookupEnvId envId config.envs
    let compiled := compileDecs [] 1 config.next initial ⟨0, config.envs.next, .ln⟩ decs
    let gen := compiled.2.2.2.1
    ∃ mapGen, Flapjack.sptLookup gen.generation (incCompileProg envId config decs).1.envs.envGens =
        some mapGen ∧
      Flapjack.sptLookup gen.next mapGen = some (extendEnv compiled.2.2.1 initial) := by
  dsimp only
  generalize h : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs = result
  rcases result with ⟨n, indices, env, gen, compiledDecs⟩
  have generation : gen.generation = config.envs.next := by
    exact OracleInvariant.compileDecs_generation [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs n indices env gen compiledDecs h
  refine ⟨Flapjack.sptInsert gen.next (extendEnv env (lookupEnvId envId config.envs)) gen.envs, ?_, ?_⟩
  · simp [incCompileProg, h, generation, Flapjack.sptLookup_sptInsert_same]
  · simpa [h] using Flapjack.sptLookup_sptInsert_same gen.next
      (extendEnv env (lookupEnvId envId config.envs)) gen.envs

/-- After incremental declaration compilation, the forward-oracle relation
retains the map for the newly extended source environment. This supplies the
lookup premise of the factored environment-ID store step. -/
theorem evalDeclaredEnvMap_factored {C : Type}
    (interp : Option (Value → Option (Config × C))) (envId : Nat × Nat)
    (config next : Config) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (before after : Option EvalState) (oldGenv newGenv : GlobalEnv)
    (sourceEnv sourceNew : SemEnv Value)
    (compiled : incCompileProg envId config decs = (next, flatDecs))
    (nextCfg : OracleInvariant.srcOracNextCfg interp before = some next)
    (forward : OracleInvariant.oracForwardRel interp before after)
    (growth : GlobalGrowth oldGenv newGenv)
    (baseInv : GlobalEnvInv oldGenv (lookupEnvId envId config.envs) (fun _ => False) sourceEnv)
    (newDomain : EnvDomainEq
      (compileDecs [] 1 config.next (lookupEnvId envId config.envs) ⟨0, config.envs.next, .ln⟩ decs).2.2.1
      sourceNew)
    (newInv : GlobalEnvInv newGenv
      (compileDecs [] 1 config.next (lookupEnvId envId config.envs) ⟨0, config.envs.next, .ln⟩ decs).2.2.1
      (fun _ => False) sourceNew) :
    let compiledDecs := compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs
    let gen := compiledDecs.2.2.2.1
    ∀ current, OracleInvariant.srcOracNextCfg interp after = some current →
      ∃ mapGen compMap, Flapjack.sptLookup gen.generation current.envs.envGens = some mapGen ∧
        Flapjack.sptLookup gen.next mapGen = some compMap ∧
        GlobalEnvInv newGenv compMap (fun _ => False) (extendDecEnv sourceNew sourceEnv) := by
  dsimp only
  intro current currentCfg
  have sub : Flapjack.sptSubspt next.envs.envGens current.envs.envGens := by
    simpa [OracleInvariant.oracConfigEnvsSubspt, nextCfg, currentCfg] using forward.1
  obtain ⟨mapGen, lookup, stored⟩ := incCompileProg_declaredEnvMap envId config decs
  have lookupNext := lookup
  rw [compiled] at lookupNext
  have lookupCurrent := (Flapjack.sptSubsptLookup _ _).mp sub _ _ lookupNext
  have baseNew := globalEnvInv_growth oldGenv newGenv growth (lookupEnvId envId config.envs)
    (fun _ => False) sourceEnv baseInv
  exact ⟨mapGen, _, lookupCurrent, stored,
    globalEnvInv_append_factored newGenv _ _ sourceNew sourceEnv ⟨newDomain, newInv, baseNew⟩⟩

/-- The Eval success path can declare its extended environment and execute
the generated ID store using the compiler map retained by the oracle. This
uses the factored simulation relations and is not yet the full HOL App case. -/
theorem evalDeclare_store_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (envId : Nat × Nat) (config next : Config) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (before : Option EvalState) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (oldGenv newGenv : GlobalEnv) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (sourceEnv sourceNew : SemEnv Value) (value : Value) (after : Option EvalState)
    (compiled : incCompileProg envId config decs = (next, flatDecs))
    (nextCfg : OracleInvariant.srcOracNextCfg interp before = some next)
    (forward : OracleInvariant.oracForwardRel interp before source.evalState)
    (growth : GlobalGrowth oldGenv newGenv)
    (baseInv : GlobalEnvInv oldGenv (lookupEnvId envId config.envs) (fun _ => False) sourceEnv)
    (newDomain : EnvDomainEq
      (compileDecs [] 1 config.next (lookupEnvId envId config.envs) ⟨0, config.envs.next, .ln⟩ decs).2.2.1
      sourceNew)
    (newInv : GlobalEnvInv newGenv
      (compileDecs [] 1 config.next (lookupEnvId envId config.envs) ⟨0, config.envs.next, .ln⟩ decs).2.2.1
      (fun _ => False) sourceNew)
    (invariant : OracleInvariant.factoredInvariant interp transform
      (compileDecs [] 1 config.next (lookupEnvId envId config.envs) ⟨0, config.envs.next, .ln⟩ decs).2.2.2.1
      newGenv idxs source flat)
    (generation : OracleInvariant.envGenRel
      (compileDecs [] 1 config.next (lookupEnvId envId config.envs) ⟨0, config.envs.next, .ln⟩ decs).2.2.2.1
      source.evalState)
    (declared : declareEnv source.evalState (extendDecEnv sourceNew sourceEnv) = some (value, after)) :
    let gen := (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs).2.2.2.1
    ∃ stored : FlatSem.Value,
      FlatSem.evaluateDecs flat [storeEnvId gen.generation gen.next] =
        ({ flat with refs := .refv stored :: flat.refs.tail }, none) ∧
      OracleInvariant.factoredInvariant interp transform { gen with next := gen.next + 1 } newGenv idxs
        { source with evalState := after } flat ∧
      OracleInvariant.factoredInvariant interp transform { gen with next := gen.next + 1 } newGenv idxs
        { source with evalState := after } { flat with refs := .refv stored :: flat.refs.tail } ∧
      (∃ globals, flat.globals = some (.loc true 0) :: globals) ∧
      ValueRel newGenv value stored ∧ OracleInvariant.oracForwardRel interp source.evalState after ∧
      OracleInvariant.envGenRel { gen with next := gen.next + 1 } after := by
  dsimp only
  have newMap := evalDeclaredEnvMap_factored interp envId config next decs flatDecs before source.evalState
    oldGenv newGenv sourceEnv sourceNew compiled nextCfg forward growth baseInv newDomain newInv
  let gen := (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
    ⟨0, config.envs.next, .ln⟩ decs).2.2.2.1
  have mapCase : (match OracleInvariant.srcOracNextCfg interp source.evalState with
      | none => True
      | some cfg =>
        match Flapjack.sptLookup gen.generation cfg.envs.envGens with
        | none => False
        | some mapGen =>
          match Flapjack.sptLookup gen.next mapGen with
          | none => False
          | some compMap => GlobalEnvInv newGenv compMap (fun _ => False) (extendDecEnv sourceNew sourceEnv)) := by
    cases cfg : OracleInvariant.srcOracNextCfg interp source.evalState with
    | none => trivial
    | some cfgValue =>
      obtain ⟨mapGen, compMap, genLookup, mapLookup, inv⟩ := newMap cfgValue cfg
      simpa [gen, genLookup, mapLookup] using inv
  have nextGeneration : OracleInvariant.envGenRel { gen with next := gen.next + 1 } after := by
    obtain ⟨_, _, _, _, _, oracle, _, _, _, _⟩ := invariant
    cases sourceState : source.evalState with
    | none => simp [sourceState, declareEnv] at declared
    | some mode =>
      obtain ⟨_, state, _, modeEq⟩ := OracleInvariant.oracRel_some interp transform mode flat.evalConfig
        (by simpa [sourceState] using oracle)
      subst mode
      exact OracleInvariant.declareEnv_oracle_generation state gen _ value after
        (by simpa [gen, sourceState] using generation) (by simpa [sourceState] using declared)
  obtain ⟨stored, run, nextInvariant, globals, related, nextForward⟩ :=
    OracleInvariant.declareEnv_storeEnvId source (extendDecEnv sourceNew sourceEnv) value after
      interp transform gen newGenv idxs flat gen.generation gen.next
      ⟨declared, invariant, generation, rfl, rfl, mapCase⟩
  exact ⟨stored, run, nextInvariant,
    OracleInvariant.factoredInvariant_changeEvalRef interp transform _ newGenv idxs _ flat stored nextInvariant,
    globals, related, nextForward, nextGeneration⟩

/-- Compose the successful declaration induction hypothesis with the actual
incremental flat sequence and its environment-ID store. The evaluator and
factored relations remain under HOL correspondence review. -/
theorem evalDeclare_incremental_success {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (envId : Nat × Nat) (config nextConfig : Config) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (before : Option EvalState) (source : SemanticPrimitivesHOL.State F)
    (flatStart flatMiddle : FlatSem.State C F) (oldGenv newGenv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (sourceEnv sourceNew : SemEnv Value) (value : Value) (after : Option EvalState)
    (n : Nat) (next : NextIndices) (newMap : Environment) (gen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp)
    (compiled : incCompileProg envId config decs = (nextConfig, flatDecs))
    (compiledBody : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, newMap, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { flatStart with globals := flatStart.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (flatMiddle, none))
    (nextCfg : OracleInvariant.srcOracNextCfg interp before = some nextConfig)
    (forward : OracleInvariant.oracForwardRel interp before source.evalState)
    (growth : GlobalGrowth oldGenv newGenv)
    (baseInv : GlobalEnvInv oldGenv (lookupEnvId envId config.envs) (fun _ => False) sourceEnv)
    (newDomain : EnvDomainEq newMap sourceNew)
    (newInv : GlobalEnvInv newGenv newMap (fun _ => False) sourceNew)
    (invariant : OracleInvariant.factoredInvariant interp transform gen newGenv idxs source flatMiddle)
    (generation : OracleInvariant.envGenRel gen source.evalState)
    (declared : declareEnv source.evalState (extendDecEnv sourceNew sourceEnv) = some (value, after)) :
    ∃ stored : FlatSem.Value,
      FlatSem.evaluateDecs flatStart flatDecs =
        ({ flatMiddle with refs := .refv stored :: flatMiddle.refs.tail }, none) ∧
      OracleInvariant.factoredInvariant interp transform { gen with next := gen.next + 1 } newGenv idxs
        { source with evalState := after } { flatMiddle with refs := .refv stored :: flatMiddle.refs.tail } ∧
      ValueRel newGenv value stored ∧ OracleInvariant.oracForwardRel interp source.evalState after ∧
      OracleInvariant.envGenRel { gen with next := gen.next + 1 } after := by
  have stage := evalDeclare_store_factored interp transform envId config nextConfig decs flatDecs before source
    flatMiddle oldGenv newGenv idxs sourceEnv sourceNew value after compiled nextCfg forward growth baseInv
    (by simpa [compiledBody] using newDomain) (by simpa [compiledBody] using newInv)
    (by simpa [compiledBody] using invariant) (by simpa [compiledBody] using generation) declared
  simp only [compiledBody] at stage
  obtain ⟨stored, storeRun, _, nextInv, _, related, nextForward, nextGeneration⟩ := stage
  have full := evaluateIncCompileProg_continue flatStart flatMiddle envId config decs n next newMap gen body
    compiledBody bodyRun
  rw [compiled] at full
  exact ⟨stored, full.trans storeRun, nextInv, related, nextForward, nextGeneration⟩

end Flapjack.Compiler.Backend.SourceToFlat
