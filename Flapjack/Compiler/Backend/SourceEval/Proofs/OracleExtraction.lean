import Flapjack.Compiler.Backend.SourceEval.Proofs
import Flapjack.EvaluateHOL.Definition
import Flapjack.HolArb
import Flapjack.Misc.OptionLeast

/-! Recording-state projection and oracle extraction for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.EvaluateHOL
open Flapjack.Basis.Pure.MlString

/-- HOL's fallback is the shared arbitrary function applied to the literal
`"not EvalOracle"`, including for both non-oracle cases. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "orac_s_def"]
noncomputable def oracleState (state : Option EvalState) : EvalOracleState :=
  let _ : Nonempty EvalOracleState :=
    ⟨⟨fun _ => ((0, 0), .conv none [], []), fun _ _ => none, [], 0⟩⟩
  match state with
  | some (.evalOracle es) => es
  | _ => Flapjack.holArb (List HolChar → EvalOracleState)
      [110, 111, 116, 32, 69, 118, 97, 108, 79, 114, 97, 99, 108, 101]

/-- Recover the next recorded event at the least clock that contains it. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "extract_oracle_def"]
noncomputable def extractOracle {σ : Type} (state : State σ) (env : SemEnv Value)
    (decs : List Dec) (n : Nat) : Option CompilerArgs :=
  match Flapjack.holOLeast (fun k => ∃ state' result,
    evaluateDecs { state with clock := k } env decs = (state', result) ∧
      n < ((oracleState state'.evalState).oracle 0).1.1) with
  | none => none
  | some k =>
    let (state', _) := evaluateDecs { state with clock := k } env decs
    some ((oracleState state'.evalState).oracle (n + 1))

end Flapjack.Compiler.Backend.SourceEval.Proofs
