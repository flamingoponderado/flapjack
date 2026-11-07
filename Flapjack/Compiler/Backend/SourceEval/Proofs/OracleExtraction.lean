import Flapjack.Compiler.Backend.SourceEval.Proofs
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleCallback
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording
import Flapjack.EvaluateHOL.Definition
import Flapjack.HolArb
import Flapjack.Misc.OptionLeast
import Lean.Elab.Tactic.Omega

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

/-- A recorded successor event implies that its predecessor can be extracted. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "extract_oracle_SOME_SUC"]
theorem extractOracle_isSome_succ {F : Type} (s : State F) (env : SemEnv Value)
    (decs : List Dec) (i : Nat) (success : (extractOracle s env decs (i + 1)).isSome) :
    (extractOracle s env decs i).isSome := by
  classical
  by_cases later : ∃ k next res,
      evaluateDecs { s with clock := k } env decs = (next, res) ∧
        i + 1 < ((oracleState next.evalState).oracle 0).1.1
  · obtain ⟨k, next, res, run, bound⟩ := later
    have earlier : ∃ k next res,
        evaluateDecs { s with clock := k } env decs = (next, res) ∧
          i < ((oracleState next.evalState).oracle 0).1.1 :=
      ⟨k, next, res, run, by omega⟩
    simp only [extractOracle, Flapjack.holOLeast, dif_pos earlier]
    cases evaluateDecs { s with clock := Nat.find earlier } env decs
    rfl
  · simp only [extractOracle, Flapjack.holOLeast, dif_neg later] at success
    contradiction

/-- Extract events from evaluation with the original initial recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "get_oracle_def"]
noncomputable def getOracle {Config F : Type} (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : Nat → Option CompilerArgs :=
  let recorded : EvalState := .evalOracle ⟨fun _ => ((0, 0), ci.configV ci.initState, []),
    doEvalRecord ci, [[]], 0⟩
  extractOracle { state with evalState := some recorded } env decs

/-- Install an oracle into the original initial recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "put_oracle_def"]
noncomputable def putOracle {Config : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun) :
    Option EvalState :=
  insertGenOracle ci id (fun args => args.1.1) oracle
    (some (.evalOracle ⟨fun _ => ((0, 0), ci.configV ci.initState, []), doEvalRecord ci, [[]], 0⟩))

/-- The original precondition for replacing an initial evaluator oracle. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "precond_eval_state_def"]
noncomputable def precondEvalState {Config F : Type} (oracle : EvalOracleFun)
    (ci : CompilerInstance Config) (state : State F) (env : SemEnv Value) (decs : List Dec) : Prop :=
  match state.evalState with
  | none => True
  | some (.evalDecs eds) =>
    .evalDecs eds = mkInitEvalState ci ∧
      oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧
      ∀ i r x, getOracle ci state env decs i = some r ∧ mkCompilerFunFromCi ci r = some x →
        oracle i = r
  | some (.evalOracle _) => False

end Flapjack.Compiler.Backend.SourceEval.Proofs
