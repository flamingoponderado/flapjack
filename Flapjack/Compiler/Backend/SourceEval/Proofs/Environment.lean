import Flapjack.Compiler.Backend.SourceEval.Proofs

/-! Environment relation used by the source evaluator proof. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Equal constructor environments and namespace domains, with related values
at every identifier present in both environments. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_def"]
def envRel {α : Type} (rel : Value → α → Prop)
    (env : SemEnv Value) (env' : SemEnv α) : Prop :=
  env.c = env'.c ∧ nsDom env.v = nsDom env'.v ∧
    nsDomMod env.v = nsDomMod env'.v ∧
    ∀ name x y, nsLookup env.v name = some x ∧ nsLookup env'.v name = some y → rel x y

/-- Pointwise weakening of the value relation preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_mono_rel"]
theorem envRel_monoRel {α : Type} (rel rel' : Value → α → Prop)
    (monotone : ∀ y z, rel y z → rel' y z)
    (env : SemEnv Value) (env' : SemEnv α) (related : envRel rel env env') :
    envRel rel' env env' := by
  obtain ⟨constructors, domain, modules, values⟩ := related
  exact ⟨constructors, domain, modules, fun name x y found => monotone x y (values name x y found)⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
