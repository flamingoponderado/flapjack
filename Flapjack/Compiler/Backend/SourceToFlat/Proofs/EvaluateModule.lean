import Flapjack.NamespaceProps.Lift
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
  exact ⟨nsDom_lift_eq moduleName _ _ values,
    nsDomMod_lift_eq moduleName _ _ valueModules,
    nsDom_lift_eq moduleName _ _ constructors,
    nsDomMod_lift_eq moduleName _ _ constructorModules⟩

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


end Flapjack.Compiler.Backend.SourceToFlat
