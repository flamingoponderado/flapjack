import Flapjack.SemanticPrimitivesHOL.Eval
import Flapjack.Misc.ShiftSeq
import Flapjack.Misc.Option

/-! Counterpart of the source evaluator proof script's Eval oracle callback. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "compiler_instance"]
structure CompilerInstance (Config : Type) where
  compilerFun : (Nat × Nat) × Config × List Dec → Option (Config × List (BitVec 8) × List (BitVec 64))
  configV : Config → Value
  configDom : Config → Prop
  decsV : List Dec → Value
  decsDom : List Dec → Prop
  initState : Config

/-- Optional choice is unspecified when several values have the same encoding. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_abs"]
noncomputable def vFunAbs {α β : Type} (dom : α → Prop) (encode : α → β)
    (value : β) : Option α :=
  Flapjack.holOptionSome (fun x => encode x = value ∧ dom x)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "mk_compiler_fun_from_ci_def"]
noncomputable def mkCompilerFunFromCi {Config : Type} (ci : CompilerInstance Config) : CompilerFun :=
  fun (envId, configValue, decs) => do
    let config ← vFunAbs ci.configDom ci.configV configValue
    let (nextConfig, bytes, words) ← ci.compilerFun (envId, config, decs)
    some (ci.configV nextConfig, bytes, words)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "mk_init_eval_state_def"]
noncomputable def mkInitEvalState {Config : Type} (ci : CompilerInstance Config) : EvalState :=
  .evalDecs ⟨mkCompilerFunFromCi ci, ci.configV ci.initState, (0, 0, 1),
    vFunAbs ci.decsDom ci.decsV⟩

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

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_gen_oracle_def"]
noncomputable def insertGenOracle {Config : Type} (ci : CompilerInstance Config)
    (transform : List Dec → List Dec) (shift : CompilerArgs → Nat)
    (oracle : EvalOracleFun) (state : Option EvalState) : Option EvalState :=
  match state with
  | some (.evalOracle s) => some (.evalOracle { s with
      customDoEval := doEvalOracle (mkCompilerFunFromCi ci) transform
      oracle := Flapjack.holShiftSeq (shift (s.oracle 0)) oracle })
  | _ => state

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_def"]
noncomputable def adjustOracle {Config : Type} (ci : CompilerInstance Config)
    (transform : List Dec → List Dec) (state : Option EvalState) : Option EvalState :=
  match state with
  | some (.evalOracle s) => some (.evalOracle { s with
      customDoEval := doEvalOracle (mkCompilerFunFromCi ci) transform })
  | _ => state

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "is_insert_oracle_def"]
def isInsertOracle {Config : Type} (ci : CompilerInstance Config)
    (transform : List Dec → List Dec) (state : Option EvalState) : Prop :=
  ∃ state' shift oracle, state = insertGenOracle ci transform shift oracle state'

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_insert_gen_oracle"]
theorem adjustOracle_insertGenOracle {Config : Type} (ci : CompilerInstance Config)
    (f g : List Dec → List Dec) (shift : CompilerArgs → Nat)
    (oracle : EvalOracleFun) (state : Option EvalState) :
    adjustOracle ci f (insertGenOracle ci g shift oracle state) =
      insertGenOracle ci f shift oracle state := by
  cases state with
  | none => rfl
  | some state => cases state <;> rfl

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
