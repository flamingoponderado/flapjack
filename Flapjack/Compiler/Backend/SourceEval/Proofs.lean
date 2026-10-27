import Flapjack.SemanticPrimitivesHOL.Eval
import Flapjack.Misc.ShiftSeq

/-! Counterpart of the source evaluator proof script's Eval oracle callback. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- The source Eval oracle checks the supplied byte and word lists against the
compiler output and advances the oracle when the next compiler state agrees.
HOL's inner pattern shadows the fourth input value, so the first four values
are used only to require exactly six inputs. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "do_eval_oracle_def"]
noncomputable def doEvalOracle (compiler : CompilerFun) (transform : List Dec → List Dec)
    (values : List Value) (oracle : EvalOracleFun) :
    Option ((Nat × Nat) × EvalOracleFun × List Dec) := by
  classical
  exact match values with
  | [_, _, _, _, bytesValue, wordsValue] =>
    let (envId, stateValue, decs) := oracle 0
    match compiler (envId, stateValue, decs), valueToWord8List bytesValue, valueToWord64List wordsValue with
    | some (nextValue, compilerBytes, compilerWords), some bytes, some words =>
      if bytes = compilerBytes ∧ words = compilerWords ∧ nextValue = (oracle 1).2.1 then
        some (envId, Flapjack.holShiftSeq 1 oracle, transform decs)
      else none
    | _, _, _ => none
  | _ => none

/-- A successful source callback advances exactly one oracle entry when the
compiled bytes, words, and next state agree. -/
theorem doEvalOracle_success (compiler : CompilerFun) (transform : List Dec → List Dec)
    (oracle : EvalOracleFun) (first second third fourth bytesValue wordsValue : Value)
    (envId : Nat × Nat) (stateValue nextValue : Value) (decs : List Dec)
    (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (entry : oracle 0 = (envId, stateValue, decs))
    (compiled : compiler (envId, stateValue, decs) = some (nextValue, bytes, words))
    (decodedBytes : valueToWord8List bytesValue = some bytes)
    (decodedWords : valueToWord64List wordsValue = some words)
    (next : nextValue = (oracle 1).2.1) :
    doEvalOracle compiler transform [first, second, third, fourth, bytesValue, wordsValue] oracle =
      some (envId, Flapjack.holShiftSeq 1 oracle, transform decs) := by
  simp [doEvalOracle, entry, compiled, decodedBytes, decodedWords, next]

/-- A successful six-argument callback exposes exactly the compiler output
and decoded lists checked by the original oracle. -/
theorem doEvalOracle_six_inv (compiler : CompilerFun) (transform : List Dec → List Dec)
    (oracle : EvalOracleFun) (first second third fourth bytesValue wordsValue : Value)
    (envId : Nat × Nat) (stateValue : Value) (decs : List Dec)
    (result : (Nat × Nat) × EvalOracleFun × List Dec)
    (entry : oracle 0 = (envId, stateValue, decs))
    (success : doEvalOracle compiler transform [first, second, third, fourth, bytesValue, wordsValue] oracle = some result) :
    ∃ nextValue bytes words,
      compiler (envId, stateValue, decs) = some (nextValue, bytes, words) ∧
      valueToWord8List bytesValue = some bytes ∧ valueToWord64List wordsValue = some words ∧
      nextValue = (oracle 1).2.1 ∧ result = (envId, Flapjack.holShiftSeq 1 oracle, transform decs) := by
  classical
  cases compiled : compiler (envId, stateValue, decs) with
  | none => simp [doEvalOracle, entry, compiled] at success
  | some output =>
    obtain ⟨nextValue, bytes, words⟩ := output
    cases byteResult : valueToWord8List bytesValue with
    | none => simp [doEvalOracle, entry, compiled, byteResult] at success
    | some decodedBytes =>
      cases wordResult : valueToWord64List wordsValue with
      | none => simp [doEvalOracle, entry, compiled, byteResult, wordResult] at success
      | some decodedWords =>
        simp [doEvalOracle, entry, compiled, byteResult, wordResult] at success
        obtain ⟨⟨sameBytes, sameWords, sameState⟩, resultEq⟩ := success
        cases sameBytes
        cases sameWords
        exact ⟨nextValue, bytes, words, rfl, rfl, rfl, sameState, resultEq.symm⟩

/-- A successful source oracle callback receives exactly six values. -/
theorem doEvalOracle_success_length (compiler : CompilerFun) (transform : List Dec → List Dec)
    (values : List Value) (oracle : EvalOracleFun) (result : (Nat × Nat) × EvalOracleFun × List Dec)
    (success : doEvalOracle compiler transform values oracle = some result) : values.length = 6 := by
  unfold doEvalOracle at success
  split at success <;> simp_all

end Flapjack.Compiler.Backend.SourceEval.Proofs
