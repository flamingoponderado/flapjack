import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentLookup
import Flapjack.NamespaceProps.Append
import Flapjack.SemanticPrimitivesHOL.Control

/-! Environment relation under namespace and declaration append. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Related namespaces preserve the environment relation when appended. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_nsAppend"]
theorem envRel_nsAppend {α β γ : Type} (rel : Value → α → Prop)
    (env : SemEnv β) (a : Namespace ModN VarN Value) (env' : SemEnv γ)
    (c : Namespace ModN VarN α) (b : Namespace ModN VarN Value) (d : Namespace ModN VarN α)
    (premises : envRel rel { env with v := a } { env' with v := c } ∧
      envRel rel { env with v := b } { env' with v := d }) :
    envRel rel { env with v := nsAppend a b } { env' with v := nsAppend c d } := by
  obtain ⟨first, second⟩ := premises
  have firstCopy := first
  have secondCopy := second
  obtain ⟨constructors, firstDom, firstMod, _⟩ := first
  obtain ⟨_, secondDom, secondMod, _⟩ := second
  refine ⟨constructors, nsDom_append_preserved a b c d firstDom secondDom firstMod,
    nsDomMod_append_preserved a b c d firstMod secondMod, ?_⟩
  intro id x y found
  obtain ⟨target, targetFound, related⟩ := nsLookup_append_transfer c d a b
    firstDom.symm firstMod.symm id x rel
    (fun _ lookup => envRel_nsLookup_v rel _ _ id _ ⟨firstCopy, lookup⟩)
    (fun _ lookup => envRel_nsLookup_v rel _ _ id _ ⟨secondCopy, lookup⟩) found.1
  rw [found.2, Option.some.injEq] at targetFound
  simpa [targetFound] using related

/-- Extending related declaration environments preserves their relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_extend_dec_env"]
theorem envRel_extendDecEnv (rel : Value → Value → Prop)
    (env₁ env₂ env₃ env₄ : SemEnv Value)
    (premises : envRel rel env₁ env₂ ∧ envRel rel env₃ env₄) :
    envRel rel (extendDecEnv env₁ env₃) (extendDecEnv env₂ env₄) := by
  obtain ⟨first, second⟩ := premises
  have constructors : env₁.c = env₂.c ∧ env₃.c = env₄.c := ⟨first.1, second.1⟩
  have appended := envRel_nsAppend rel env₁ env₁.v env₂ env₂.v env₃.v env₄.v
    ⟨first, ⟨first.1, second.2⟩⟩
  exact ⟨by simp [extendDecEnv, constructors.1, constructors.2], appended.2⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
