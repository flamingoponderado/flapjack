import Flapjack.Compiler.Backend.SourceEval.Proofs.Environment
import Flapjack.NamespaceProps.Lift

/-! Source evaluator environment relation under module lifting. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Lifting two related environments under the same module preserves their relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_nsLift"]
theorem envRel_nsLift {α β γ : Type} (rel : Value → α → Prop)
    (env : SemEnv β) (v : Namespace ModN VarN Value) (c : Namespace ModN ConN (Nat × Stamp))
    (env' : SemEnv γ) (v' : Namespace ModN VarN α) (c' : Namespace ModN ConN (Nat × Stamp))
    (mn : ModN)
    (related : envRel rel { env with v := v, c := c } { env' with v := v', c := c' }) :
    envRel rel { env with v := nsLift mn v, c := nsLift mn c }
      { env' with v := nsLift mn v', c := nsLift mn c' } := by
  obtain ⟨constructors, domain, modules, values⟩ := related
  change c = c' at constructors
  refine ⟨by rw [constructors], nsDom_lift_eq mn v v' domain,
    nsDomMod_lift_eq mn v v' modules, ?_⟩
  intro id x y found
  cases id with
  | short name => simp [nsLift, nsLookup] at found
  | long head rest =>
    by_cases same : head = mn
    · subst head
      apply values rest x y
      simpa [nsLift, nsLookup] using found
    · simp [nsLift, nsLookup, List.lookup, BEq.beq, same] at found

end Flapjack.Compiler.Backend.SourceEval.Proofs
