module

public import Flapjack.SemanticPrimitivesHOL.Eval

@[expose] public section

/-! Concrete values produced by the source evaluator's decoders. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_list_concrete"]
theorem valueToList_concrete (value : Value) (values : List Value)
    (decoded : valueToList value = some values) :
    concreteValue value = values.all concreteValue := by
  fun_induction valueToList value generalizing values <;>
    simp_all [concreteValue, concreteValues]
  obtain ⟨tailValues, tailDecoded, rfl⟩ := decoded
  simp_all

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "maybe_all_list_SOME"]
theorem maybeAllList_some {α : Type} (xs : List (Option α)) (ys : List α)
    (decoded : maybeAllList xs = some ys) : xs = ys.map some :=
  maybeAllList_reconstruct xs ys decoded

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "maybe_all_list_EVERY"]
theorem maybeAllList_every {α : Type} (xs : List (Option α)) (ys : List α)
    (decoded : maybeAllList xs = some ys) : ∀ x ∈ xs, x ≠ none := by
  rw [maybeAllList_some xs ys decoded]
  simp

/-- Shared proof infrastructure for decoders whose successful elements are
concrete; the original HOL word-list theorems instantiate this argument. -/
private theorem decodedList_concrete {α : Type} (decode : Value → Option α)
    (elementConcrete : ∀ v, decode v ≠ none → concreteValue v = true)
    (value : Value) (decodedValues : List Value) (results : List α)
    (decoded : valueToList value = some decodedValues)
    (collected : maybeAllList (decodedValues.map decode) = some results) :
    concreteValue value = true := by
  rw [valueToList_concrete value decodedValues decoded]
  apply List.all_eq_true.mpr
  intro v member
  apply elementConcrete v
  exact maybeAllList_every _ _ collected (decode v) (List.mem_map.mpr ⟨v, member, rfl⟩)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_word8_list_concrete"]
theorem valueToWord8List_concrete (value : Value) (bytes : List (BitVec 8))
    (decoded : valueToWord8List value = some bytes) : concreteValue value = true := by
  cases found : valueToList value with
  | none => simp [valueToWord8List, found] at decoded
  | some values =>
    apply decodedList_concrete valueToWord8 _ value values bytes found
      (by simpa [valueToWord8List, found] using decoded)
    intro v success
    cases v with
    | litv lit => cases lit <;> simp_all [valueToWord8, concreteValue]
    | _ => simp [valueToWord8] at success

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_word64_list_concrete"]
theorem valueToWord64List_concrete (value : Value) (words : List (BitVec 64))
    (decoded : valueToWord64List value = some words) : concreteValue value = true := by
  cases found : valueToList value with
  | none => simp [valueToWord64List, found] at decoded
  | some values =>
    apply decodedList_concrete valueToWord64 _ value values words found
      (by simpa [valueToWord64List, found] using decoded)
    intro v success
    cases v with
    | litv lit => cases lit <;> simp_all [valueToWord64, concreteValue]
    | _ => simp [valueToWord64] at success

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "compiler_agrees"]
theorem compilerAgrees_concrete (compiler : CompilerFun) (id : Nat × Nat)
    (state : Value) (decs : List Flapjack.AstHOL.Dec) (next bytes words : Value)
    (agrees : compilerAgrees compiler (id, state, decs) (next, bytes, words)) :
    concreteValue state = true ∧ concreteValue next = true ∧
      concreteValue bytes = true ∧ concreteValue words = true := by
  cases output : compiler (id, state, decs) with
  | none => simp [compilerAgrees, output] at agrees
  | some result =>
    obtain ⟨nextState, byteList, wordList⟩ := result
    cases byteDecoded : valueToWord8List bytes with
    | none => simp [compilerAgrees, output, byteDecoded] at agrees
    | some decodedBytes =>
      cases wordDecoded : valueToWord64List words with
      | none => simp [compilerAgrees, output, byteDecoded, wordDecoded] at agrees
      | some decodedWords =>
        simp [compilerAgrees, output, byteDecoded, wordDecoded] at agrees
        exact ⟨agrees.2.2.2.2, agrees.2.2.2.1,
          valueToWord8List_concrete bytes decodedBytes byteDecoded,
          valueToWord64List_concrete words decodedWords wordDecoded⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
