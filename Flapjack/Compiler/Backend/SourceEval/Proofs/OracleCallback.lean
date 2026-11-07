import Flapjack.Compiler.Backend.SourceEval.Proofs

/-! The source evaluator's recording callback and its input decoders. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_nat_def"]
def valueToNat : Value → Option Nat
  | .litv (.intLit i) => if 0 ≤ i then some i.toNat else none
  | _ => none

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_env_id_def"]
def valueToEnvId : Value → Option (Nat × Nat)
  | .conv none [generation, id] =>
      match valueToNat generation, valueToNat id with
      | some generation, some id => some (generation, id)
      | _, _ => none
  | _ => none

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "do_eval_record_def"]
noncomputable def doEvalRecord {Config : Type} (ci : CompilerInstance Config)
    (values : List Value) (oracle : EvalOracleFun) :
    Option ((Nat × Nat) × EvalOracleFun × List Dec) := by
  classical
  exact match values with
  | [envIdValue, stateValue, decsValue, nextValue, bytesValue, wordsValue] =>
    let ((i, _), state, _) := oracle 0
    match valueToEnvId envIdValue, vFunAbs ci.decsDom ci.decsV decsValue with
    | some envId, some decs =>
      if compilerAgrees (mkCompilerFunFromCi ci) (envId, stateValue, decs)
          (nextValue, bytesValue, wordsValue) ∧ stateValue = state then
        let updated := fun j =>
          if j = 0 then ((i + 1, 0), nextValue, [])
          else if j = i + 1 then (envId, state, decs) else oracle j
        some (envId, updated, decs)
      else none
    | _, _ => none
  | _ => none

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "is_record_def"]
def isRecord {Config : Type} (ci : CompilerInstance Config) (state : Option EvalState) : Prop :=
  match state with
  | some (.evalOracle s) => s.customDoEval = doEvalRecord ci
  | _ => False

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "is_record_IMP"]
theorem isRecord_imp {Config : Type} (ci : CompilerInstance Config) (state : Option EvalState)
    (recording : isRecord ci state) : ∃ oracleState, state = some (.evalOracle oracleState) := by
  cases state with
  | none => cases recording
  | some s =>
    cases s with
    | evalDecs _ => cases recording
    | evalOracle s => exact ⟨s, rfl⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
