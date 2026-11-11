module

public import Flapjack.NamespaceProps.Lift
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateSequence

@[expose] public section

/-! Module declaration simulation over the preliminary factored relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

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
      | short name => simp [nsLookup_nsLift] at lookup
      | long head rest =>
        by_cases same : head = moduleName
        · subst head
          have inner : nsLookup sourceEnv.v rest = some value := by simpa [nsLookup_nsLift] using lookup
          have related := values rest value (by simp) inner
          cases related with
          | intro _ _ _ idx flat trace compiled bound slot relation =>
            exact .intro _ _ _ _ idx flat trace (by simpa [liftEnv, nsLookup_nsLift] using compiled) bound slot relation
        · simp [nsLookup_nsLift, Ne.symm same] at lookup
    · intro id arity stamp lookup
      cases id with
      | short name => simp [nsLookup_nsLift] at lookup
      | long head rest =>
        by_cases same : head = moduleName
        · subst head
          have inner : nsLookup sourceEnv.c rest = some (arity, stamp) := by simpa [nsLookup_nsLift] using lookup
          obtain ⟨cn, group, compiled, mapped, types⟩ := constructors rest arity stamp inner
          exact ⟨cn, group, by simpa [liftEnv, nsLookup_nsLift] using compiled, mapped, types⟩
        · simp [nsLookup_nsLift, Ne.symm same] at lookup

end Flapjack.Compiler.Backend.SourceToFlat
