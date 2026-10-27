import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv

/-! Namespace-domain facts needed by sequential declaration simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- A short lookup in an appended namespace chooses the first available
binding. -/
theorem nsLookup_append_short {M N V : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (name : N) :
    nsLookup (nsAppend first second) (.short name) =
      (nsLookup first (.short name)).orElse (fun _ => nsLookup second (.short name)) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      simp [nsAppend, nsLookup, List.lookup_append]

/-- A long lookup uses the first namespace whenever it contains the initial
module, even if the rest of the lookup fails. -/
theorem nsLookup_append_long {M N V : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (moduleName : M) (rest : Ident M N) :
    nsLookup (nsAppend first second) (.long moduleName rest) =
      match nsLookupMod first [moduleName] with
      | none => nsLookup second (.long moduleName rest)
      | some _ => nsLookup first (.long moduleName rest) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      cases found : firstModules.lookup moduleName <;>
        simp [nsAppend, nsLookup, nsLookupMod, List.lookup_append, found]

/-- Module lookup in an append has the same first-module shadowing rule. -/
theorem nsLookupMod_append_cons {M N V : Type} [DecidableEq M]
    (first second : Namespace M N V) (moduleName : M) (rest : List M) :
    nsLookupMod (nsAppend first second) (moduleName :: rest) =
      match nsLookupMod first [moduleName] with
      | none => nsLookupMod second (moduleName :: rest)
      | some _ => nsLookupMod first (moduleName :: rest) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      cases found : firstModules.lookup moduleName <;>
        simp [nsAppend, nsLookupMod, List.lookup_append, found]

/-- Corresponding namespaces retain corresponding value domains after
left-biased append, including module shadowing. -/
theorem nsDom_append_preserved {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (first' second' : Namespace M N W)
    (firstDomain : nsDom first = nsDom first') (secondDomain : nsDom second = nsDom second')
    (firstModules : nsDomMod first = nsDomMod first') :
    nsDom (nsAppend first second) = nsDom (nsAppend first' second') := by
  funext id
  apply propext
  have firstAt := congrFun firstDomain id
  have secondAt := congrFun secondDomain id
  change (∃ v, nsLookup first id = some v) = (∃ v, nsLookup first' id = some v) at firstAt
  change (∃ v, nsLookup second id = some v) = (∃ v, nsLookup second' id = some v) at secondAt
  change (∃ v, nsLookup (nsAppend first second) id = some v) ↔
    (∃ v, nsLookup (nsAppend first' second') id = some v)
  cases id with
  | short name =>
    simp only [nsLookup_append_short]
    cases h1 : nsLookup first (.short name) <;> cases h2 : nsLookup first' (.short name) <;>
      cases h3 : nsLookup second (.short name) <;> cases h4 : nsLookup second' (.short name) <;>
      simp_all
  | long moduleName rest =>
    have modulesAt := congrFun firstModules [moduleName]
    change (∃ v, nsLookupMod first [moduleName] = some v) =
      (∃ v, nsLookupMod first' [moduleName] = some v) at modulesAt
    simp only [nsLookup_append_long]
    cases h1 : nsLookupMod first [moduleName] <;> cases h2 : nsLookupMod first' [moduleName] <;>
      simp_all

/-- Module domains also agree after left-biased append. -/
theorem nsDomMod_append_preserved {M N V W : Type} [DecidableEq M]
    (first second : Namespace M N V) (first' second' : Namespace M N W)
    (firstModules : nsDomMod first = nsDomMod first')
    (secondModules : nsDomMod second = nsDomMod second') :
    nsDomMod (nsAppend first second) = nsDomMod (nsAppend first' second') := by
  funext path
  apply propext
  have firstAt := congrFun firstModules path
  have secondAt := congrFun secondModules path
  change (∃ v, nsLookupMod first path = some v) = (∃ v, nsLookupMod first' path = some v) at firstAt
  change (∃ v, nsLookupMod second path = some v) = (∃ v, nsLookupMod second' path = some v) at secondAt
  change (∃ v, nsLookupMod (nsAppend first second) path = some v) ↔
    (∃ v, nsLookupMod (nsAppend first' second') path = some v)
  cases path with
  | nil => simp [nsLookupMod]
  | cons moduleName rest =>
    have modulesAt := congrFun firstModules [moduleName]
    change (∃ v, nsLookupMod first [moduleName] = some v) =
      (∃ v, nsLookupMod first' [moduleName] = some v) at modulesAt
    simp only [nsLookupMod_append_cons]
    cases h1 : nsLookupMod first [moduleName] <;> cases h2 : nsLookupMod first' [moduleName] <;>
      simp_all

/-- Pointwise lookup correspondence is preserved by namespace extension
when the leading namespaces have the same value and module domains. -/
theorem nsLookup_append_transfer {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (first' second' : Namespace M N W)
    (firstDomain : nsDom first = nsDom first') (firstModules : nsDomMod first = nsDomMod first')
    (id : Ident M N) (value : W) (rel : W → V → Prop)
    (firstRelated : ∀ v, nsLookup first' id = some v →
      ∃ w, nsLookup first id = some w ∧ rel v w)
    (secondRelated : ∀ v, nsLookup second' id = some v →
      ∃ w, nsLookup second id = some w ∧ rel v w)
    (sourceLookup : nsLookup (nsAppend first' second') id = some value) :
    ∃ w, nsLookup (nsAppend first second) id = some w ∧ rel value w := by
  cases id with
  | short name =>
    rw [nsLookup_append_short] at sourceLookup ⊢
    cases src : nsLookup first' (.short name) with
    | some v =>
      simp [src] at sourceLookup
      subst v
      obtain ⟨w, lookup, related⟩ := firstRelated value src
      exact ⟨w, by simp [lookup], related⟩
    | none =>
      have firstNone : nsLookup first (.short name) = none := by
        have h := congrFun firstDomain (.short name)
        change (∃ v, nsLookup first (.short name) = some v) =
          (∃ v, nsLookup first' (.short name) = some v) at h
        cases found : nsLookup first (.short name) <;> simp_all
      have sourceSecond : nsLookup second' (.short name) = some value := by simpa [src] using sourceLookup
      obtain ⟨w, lookup, related⟩ := secondRelated value sourceSecond
      exact ⟨w, by simp [firstNone, lookup], related⟩
  | long moduleName rest =>
    rw [nsLookup_append_long] at sourceLookup ⊢
    have modules := congrFun firstModules [moduleName]
    change (∃ v, nsLookupMod first [moduleName] = some v) =
      (∃ v, nsLookupMod first' [moduleName] = some v) at modules
    cases srcModule : nsLookupMod first' [moduleName] with
    | none =>
      have firstNone : nsLookupMod first [moduleName] = none := by
        cases found : nsLookupMod first [moduleName] <;> simp_all
      have sourceSecond : nsLookup second' (.long moduleName rest) = some value := by
        simpa [srcModule] using sourceLookup
      obtain ⟨w, lookup, related⟩ := secondRelated value sourceSecond
      exact ⟨w, by simp [firstNone, lookup], related⟩
    | some sourceModule =>
      have firstSome : ∃ targetModule, nsLookupMod first [moduleName] = some targetModule := by
        cases found : nsLookupMod first [moduleName] <;> simp_all
      obtain ⟨targetModule, targetLookup⟩ := firstSome
      have sourceFirst : nsLookup first' (.long moduleName rest) = some value := by
        simpa [srcModule] using sourceLookup
      obtain ⟨w, lookup, related⟩ := firstRelated value sourceFirst
      exact ⟨w, by simp [targetLookup, lookup], related⟩

/-- Extending compiler and source environments preserves their value,
constructor, and module domains. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_domain_eq_append"]
theorem envDomainEq_append (first second : Environment) (sourceFirst sourceSecond : SemEnv Value)
    (premises : EnvDomainEq first sourceFirst ∧ EnvDomainEq second sourceSecond) :
    EnvDomainEq (extendEnv first second) (extendDecEnv sourceFirst sourceSecond) := by
  obtain ⟨⟨v1, vm1, c1, cm1⟩, ⟨v2, vm2, c2, cm2⟩⟩ := premises
  exact ⟨nsDom_append_preserved _ _ _ _ v1 v2 vm1,
    nsDomMod_append_preserved _ _ _ _ vm1 vm2,
    nsDom_append_preserved _ _ _ _ c1 c2 cm1,
    nsDomMod_append_preserved _ _ _ _ cm1 cm2⟩

/-- The factored global environment invariant composes across declaration
extensions. This is untagged until the factored value and global relations
have been reviewed as corresponding to their HOL inductive relations. -/
theorem globalEnvInv_append_factored (genv : GlobalEnv)
    (first second : Environment) (sourceFirst sourceSecond : SemEnv Value)
    (domain : EnvDomainEq first sourceFirst)
    (firstInv : GlobalEnvInv genv first (fun _ => False) sourceFirst)
    (secondInv : GlobalEnvInv genv second (fun _ => False) sourceSecond) :
    GlobalEnvInv genv (extendEnv first second) (fun _ => False)
      (extendDecEnv sourceFirst sourceSecond) := by
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
    simpa [h] using OracleInvariant.compileDecs_generation_core [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs
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
    globalEnvInv_append_factored newGenv _ _ sourceNew sourceEnv newDomain newInv baseNew⟩

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
      (∃ globals, flat.globals = some (.loc true 0) :: globals) ∧
      ValueRel newGenv value stored ∧ OracleInvariant.oracForwardRel interp source.evalState after ∧
      OracleInvariant.envGenRel { gen with next := gen.next + 1 } after := by
  dsimp only
  have newMap := evalDeclaredEnvMap_factored interp envId config next decs flatDecs before source.evalState
    oldGenv newGenv sourceEnv sourceNew compiled nextCfg forward growth baseInv newDomain newInv
  exact OracleInvariant.declareEnv_storeEnvId_factored_all interp transform _ newGenv idxs source flat
    (extendDecEnv sourceNew sourceEnv) value after invariant generation declared newMap

end Flapjack.Compiler.Backend.SourceToFlat
