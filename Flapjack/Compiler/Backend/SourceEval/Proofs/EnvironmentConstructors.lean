import Flapjack.Compiler.Backend.SourceEval.Proofs.Environment

/-! Constructor-namespace equality for the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- Related environments have the same constructor namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_imp_c"]
theorem envRel_imp_c {α : Type} (rel : Value → α → Prop)
    (env : SemEnv Value) (env' : SemEnv α) (related : envRel rel env env') :
    env'.c = env.c := related.1.symm

end Flapjack.Compiler.Backend.SourceEval.Proofs
