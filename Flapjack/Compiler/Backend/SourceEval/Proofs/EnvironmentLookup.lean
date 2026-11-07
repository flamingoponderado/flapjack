import Flapjack.Compiler.Backend.SourceEval.Proofs.Environment

/-! Lookup preservation for the source evaluator's environment relation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- A source binding has a related target binding at the same identifier. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_nsLookup_v"]
theorem envRel_nsLookup_v {α : Type} (rel : Value → α → Prop)
    (env : SemEnv Value) (env' : SemEnv α) (id : Ident ModN VarN) (value : Value)
    (premises : envRel rel env env' ∧ nsLookup env.v id = some value) :
    ∃ value', nsLookup env'.v id = some value' ∧ rel value value' := by
  obtain ⟨⟨_, domains, _, values⟩, found⟩ := premises
  have present : nsDom env.v id := ⟨value, found⟩
  rw [domains] at present
  obtain ⟨value', found'⟩ := present
  exact ⟨value', found', values id value value' ⟨found, found'⟩⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
