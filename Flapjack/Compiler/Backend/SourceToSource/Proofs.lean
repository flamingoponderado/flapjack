module

public import Flapjack.Compiler.Backend.SourceToSource
public import Flapjack.Compiler.Backend.SourceLet.Proofs.Semantics

@[expose] public section

/-! Semantic preservation of the source-to-source pass driver. -/
namespace Flapjack.Compiler.Backend.SourceToSource
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticsHOL

/-- The source-to-source driver preserves the original observations whenever
the source program does not fail with a type error. -/
@[hol "cakeml/compiler/backend/proofs/source_to_sourceProofScript.sml" "compile_semantics"]
theorem compile_semantics {F : Type} (state : State F) (env : SemEnv Value)
    (program : List Dec) (outcome : HolBehaviour)
    (premises : ¬ semanticsProg state env program .fail ∧ semanticsProg state env program outcome) :
    semanticsProg state env (compile program) outcome :=
  SourceLet.compile_semantics state env program outcome premises

/-- The source-to-source driver preserves observable semantics when composed
into an inserted Eval oracle. -/
@[hol "cakeml/compiler/backend/proofs/source_to_sourceProofScript.sml" "compile_semantics_oracle"]
theorem compile_semantics_oracle {Config F : Type}
    (ci : SourceEval.Proofs.CompilerInstance Config) (state : State F) (env : SemEnv Value)
    (program : List Dec) (outcome : HolBehaviour) (f : List Dec → List Dec)
    (premises : SourceEval.Proofs.isInsertOracle ci f state.evalState ∧
      ¬ semanticsProg state env program .fail ∧ semanticsProg state env program outcome) :
    semanticsProg { state with evalState := SourceEval.Proofs.adjustOracle ci (compile ∘ f) state.evalState }
      env program outcome :=
  SourceLet.compile_semantics_oracle ci state env program outcome f premises

end Flapjack.Compiler.Backend.SourceToSource
