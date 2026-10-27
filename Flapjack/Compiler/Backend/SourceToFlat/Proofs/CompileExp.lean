import Flapjack.Compiler.Backend.SourceToFlat.CompileExp

/-! List-shape prerequisite for the source-to-flat pass correctness proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compiling an expression list preserves its length. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_exps_length"]
theorem compileExps_length (t : List Basis.Pure.MlString.MlString)
    (env : Environment) (es : List AstHOL.Exp) :
    (compileExps t env es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [compileExps, ih]

end Flapjack.Compiler.Backend.SourceToFlat
