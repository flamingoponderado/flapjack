import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateSequence

/-! Module declaration simulation over the preliminary factored relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

/-- Lifting corresponding environments into the same module preserves their
value, constructor, and module domains. -/
theorem envDomainEq_lift (moduleName : ModN) (compMap : Environment) (sourceEnv : SemEnv Value)
    (domain : EnvDomainEq compMap sourceEnv) :
    EnvDomainEq (liftEnv moduleName compMap)
      ⟨nsLift moduleName sourceEnv.v, nsLift moduleName sourceEnv.c⟩ := by
  obtain ⟨values, valueModules, constructors, constructorModules⟩ := domain
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext id
    apply propext
    cases id with
    | short name => simp [liftEnv, nsDom, nsLift, nsLookup]
    | long head rest =>
      by_cases same : head = moduleName
      · subst head
        simpa [liftEnv, nsDom, nsLift, nsLookup] using congrFun values rest
      · simp [liftEnv, nsDom, nsLift, nsLookup, List.lookup, BEq.beq, same]
  · funext path
    apply propext
    cases path with
    | nil => simp [liftEnv, nsDomMod, nsLookupMod]
    | cons head rest =>
      by_cases same : head = moduleName
      · subst head
        simpa [liftEnv, nsDomMod, nsLift, nsLookupMod] using congrFun valueModules rest
      · simp [liftEnv, nsDomMod, nsLift, nsLookupMod, List.lookup, BEq.beq, same]
  · funext id
    apply propext
    cases id with
    | short name => simp [liftEnv, nsDom, nsLift, nsLookup]
    | long head rest =>
      by_cases same : head = moduleName
      · subst head
        simpa [liftEnv, nsDom, nsLift, nsLookup] using congrFun constructors rest
      · simp [liftEnv, nsDom, nsLift, nsLookup, List.lookup, BEq.beq, same]
  · funext path
    apply propext
    cases path with
    | nil => simp [liftEnv, nsDomMod, nsLookupMod]
    | cons head rest =>
      by_cases same : head = moduleName
      · subst head
        simpa [liftEnv, nsDomMod, nsLift, nsLookupMod] using congrFun constructorModules rest
      · simp [liftEnv, nsDomMod, nsLift, nsLookupMod, List.lookup, BEq.beq, same]

/-- Lifting related environments into a module preserves the factored
global-environment invariant. -/
theorem globalEnvInv_lift (genv : GlobalEnv) (moduleName : ModN)
    (compMap : Environment) (sourceEnv : SemEnv Value)
    (invariant : GlobalEnvInv genv compMap (fun _ => False) sourceEnv) :
    GlobalEnvInv genv (liftEnv moduleName compMap) (fun _ => False)
      ⟨nsLift moduleName sourceEnv.v, nsLift moduleName sourceEnv.c⟩ := by
  cases invariant with
  | intro _ _ _ values constructors =>
    apply GlobalEnvInv.intro
    · intro id value _ lookup
      cases id with
      | short name => simp [nsLift, nsLookup] at lookup
      | long head rest =>
        by_cases same : head = moduleName
        · subst head
          have inner : nsLookup sourceEnv.v rest = some value := by simpa [nsLift, nsLookup] using lookup
          have related := values rest value (by simp) inner
          cases related with
          | intro _ _ _ idx flat trace compiled bound slot relation =>
            exact .intro _ _ _ _ idx flat trace (by simpa [liftEnv, nsLift, nsLookup] using compiled) bound slot relation
        · simp [nsLift, nsLookup, List.lookup, BEq.beq, same] at lookup
    · intro id arity stamp lookup
      cases id with
      | short name => simp [nsLift, nsLookup] at lookup
      | long head rest =>
        by_cases same : head = moduleName
        · subst head
          have inner : nsLookup sourceEnv.c rest = some (arity, stamp) := by simpa [nsLift, nsLookup] using lookup
          obtain ⟨cn, group, compiled, mapped, types⟩ := constructors rest arity stamp inner
          exact ⟨cn, group, by simpa [liftEnv, nsLift, nsLookup] using compiled, mapped, types⟩
        · simp [nsLift, nsLookup, List.lookup, BEq.beq, same] at lookup

/-- Lift the result of an inner declaration simulation into a module. The
flat code, state, index and oracle outcomes remain those of the inner case. -/
theorem factoredDecCase_liftModule {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source sourceLast : State F) (flat : FlatSem.State C F)
    (finish next : NextIndices) (other : Set (Nat × IndexKind)) (nextGen : EnvironmentGenerationStore)
    (innerMap : Environment) (moduleName : ModN) (flatDecs : List FlatLang.Exp)
    (innerResult : Result (SemEnv Value) Value)
    (inner : FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen innerMap
      flatDecs innerResult) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen
      (liftEnv moduleName innerMap) flatDecs
      (match innerResult with
       | .val resultEnv => .val ⟨nsLift moduleName resultEnv.v, nsLift moduleName resultEnv.c⟩
       | .err error => .err error) := by
  obtain ⟨finalState, finalGenv, flatError, flatRun, states, post, success, errors⟩ := inner
  refine ⟨finalState, finalGenv, flatError, flatRun, states, ?_⟩
  cases innerResult with
  | val innerEnv =>
    obtain ⟨invariant, forward, growth⟩ := post trivial
    obtain ⟨noError, domain, generation, envInv⟩ := success innerEnv rfl
    refine ⟨?_, ?_, ?_⟩
    · intro _
      exact ⟨invariant, forward, growth⟩
    · intro resultEnv same
      cases same
      exact ⟨noError, envDomainEq_lift moduleName innerMap innerEnv domain, generation,
        globalEnvInv_lift finalGenv moduleName innerMap innerEnv envInv⟩
    · intro error impossible
      cases impossible
  | err error =>
    refine ⟨?_, ?_, ?_⟩
    · cases error with
      | abort kind => intro impossible; exact False.elim impossible
      | raise value => intro _; exact post trivial
    · intro resultEnv impossible
      cases impossible
    · intro error' same
      cases same
      exact errors error rfl

/-- A module declaration satisfies the factored declaration induction
hypothesis when its inner declaration list does. -/
theorem factoredDecIH_dmod {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (moduleName : ModN) (decs : List Dec) (innerIH : FactoredDecIH (F := F) interp transform decs) :
    FactoredDecIH (F := F) interp transform [.dmod moduleName decs] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled envInv notTypeError generation future bounded
  generalize innerCompiled : compileDecs (moduleName :: trace) n start env gen decs = innerTuple
  obtain ⟨innerN, innerNext, innerEnv, innerGen, innerCode⟩ := innerTuple
  have outerCompiled : compileDecs trace n start env gen [.dmod moduleName decs] =
      (innerN, innerNext, liftEnv moduleName innerEnv, innerGen, innerCode) := by
    simp [compileDecs, innerCompiled]
  have compEq := compiled.symm.trans outerCompiled
  simp only [Prod.mk.injEq] at compEq
  obtain ⟨_, nextEq, envEq, genEq, codeEq⟩ := compEq
  subst next
  subst nextEnv
  subst nextGen
  subst flatDecs
  generalize innerRun : EvaluateHOL.evaluateDecs source sourceEnv decs = innerPair
  obtain ⟨innerLast, innerResult⟩ := innerPair
  have resultEq : sourceLast = innerLast ∧ result =
      (match innerResult with
       | .val inner => .val ⟨nsLift moduleName inner.v, nsLift moduleName inner.c⟩
       | .err error => .err error) := by
    have h := sourceRun
    simp only [EvaluateHOL.evaluateDecs, innerRun] at h
    cases innerResult <;> simp_all
  obtain ⟨lastEq, outEq⟩ := resultEq
  subst sourceLast
  subst result
  have innerSafe : innerResult ≠ .err (.abort .typeError) := by
    cases innerResult with
    | val resultEnv => simp
    | err error => simpa using notTypeError
  have inner := innerIH genv env innerEnv sourceEnv (moduleName :: trace) source innerLast flat start finish
    innerNext other n innerN gen innerGen innerCode innerResult innerRun invariant innerCompiled envInv innerSafe
    generation future bounded
  cases innerResult <;>
    exact factoredDecCase_liftModule interp transform genv source innerLast flat finish innerNext other innerGen
      innerEnv moduleName innerCode _ inner

/-- Partial proof coverage extended recursively through module declarations.
This predicate is proof bookkeeping, not a restriction on CakeML programs. -/
inductive FactoredModuleTree : Dec → Prop where
  | basic (dec : Dec) : FactoredDecSupported dec → FactoredModuleTree dec
  | module_ (moduleName : ModN) (decs : List Dec) :
      (∀ dec, dec ∈ decs → FactoredModuleTree dec) → FactoredModuleTree (.dmod moduleName decs)

/-- All module trees built from the covered base cases satisfy the factored
singleton simulation. -/
theorem factoredDecIH_moduleTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (dec : Dec) (covered : FactoredModuleTree dec) : FactoredDecIH (F := F) interp transform [dec] := by
  induction covered with
  | basic dec supported =>
    apply factoredDecIH_supported_list interp transform [dec]
    intro item member
    simp only [List.mem_singleton] at member
    subst item
    exact supported
  | module_ moduleName decs _ ih =>
    apply factoredDecIH_dmod interp transform moduleName decs
    apply factoredDecIH_list interp transform decs
    exact ih

/-- Lists of covered module trees satisfy the factored declaration
simulation, with arbitrary nesting of module declarations. -/
theorem factoredDecIH_moduleTree_list {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (decs : List Dec) (covered : ∀ dec, dec ∈ decs → FactoredModuleTree dec) :
    FactoredDecIH (F := F) interp transform decs := by
  apply factoredDecIH_list interp transform decs
  intro dec member
  exact factoredDecIH_moduleTree interp transform dec (covered dec member)
end Flapjack.Compiler.Backend.SourceToFlat
