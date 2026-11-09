module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.VectorRead

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
import all Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
@[expose] public section

/-! String construction in the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- A successful character-list decoding is also a value-list decoding with
character literals. This is an infrastructure lemma for the simulation. -/
theorem charList_valueList (source : FlatSem.Value) (chars : List HolChar)
    (decoded : FlatSem.valueToCharList source = some chars) :
    FlatSem.valueToList source = some (chars.map (.litv ∘ Lit.char)) := by
  cases source with
  | conv stamp fields =>
    cases stamp with
    | none => simp [FlatSem.valueToCharList] at decoded
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases fields with
      | nil =>
        simp only [FlatSem.valueToCharList] at decoded
        split at decoded
        · rename_i tags
          simp at decoded
          subst chars
          simp [FlatSem.valueToList, tags]
        · simp at decoded
      | cons head rest =>
        cases rest with
        | nil => simp [FlatSem.valueToCharList] at decoded
        | cons tail rest =>
          cases rest with
          | cons extra rest => simp [FlatSem.valueToCharList] at decoded
          | nil =>
            cases head with
            | litv literal =>
              cases literal with
              | char byte =>
                simp only [FlatSem.valueToCharList] at decoded
                split at decoded
                · rename_i tags
                  cases tailDecoded : FlatSem.valueToCharList tail with
                  | none => simp [tailDecoded] at decoded
                  | some tailChars =>
                    simp [tailDecoded] at decoded
                    subst chars
                    have ih := charList_valueList tail tailChars tailDecoded
                    simp [FlatSem.valueToList, tags, ih]
                · simp at decoded
              | intLit | strLit | word8 | word64 | float64 => simp [FlatSem.valueToCharList] at decoded
            | conv | closure | recclosure | loc | vectorv => simp [FlatSem.valueToCharList] at decoded
  | litv | closure | recclosure | loc | vectorv => simp [FlatSem.valueToCharList] at decoded
termination_by sizeOf source

/-- Related character literals have exactly the closure number encoding of
their byte values. -/
theorem related_charList (chars : List HolChar) (target : List ClosSem.Value)
    (related : List.Forall₂ ValueRel (chars.map (.litv ∘ Lit.char)) target) :
    target = chars.map (fun byte => .number byte.toNat) := by
  induction chars generalizing target with
  | nil => cases related; rfl
  | cons first rest ih =>
    cases related with
    | cons head tail =>
      cases head
      simp [ih _ tail]

/-- Decoding a related flat character list yields its closure number list. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "v_rel_v_to_char_list"]
theorem valueToCharList_related (source : FlatSem.Value) (chars : List HolChar)
    (target : ClosSem.Value)
    (premises : FlatSem.valueToCharList source = some chars ∧ ValueRel source target) :
    ClosSem.valueToList target = some ((chars.map (fun c => c.toNat)).map (fun n => .number (Int.ofNat n))) := by
  obtain ⟨decoded, related⟩ := premises
  have flatList := charList_valueList source chars decoded
  obtain ⟨targetValues, targetDecoded, valuesRelated⟩ :=
    valueToList_related source target _ related flatList
  rw [related_charList chars targetValues valuesRelated] at targetDecoded
  simpa [List.map_map, Function.comp_def] using targetDecoded

/-- A successfully concatenated flat list has related closure byte vectors
whose flattened bytes are the source result. -/
theorem valuesToString_related {source : List FlatSem.Value} {target : List ClosSem.Value}
    (related : List.Forall₂ ValueRel source target) (result : MlString)
    (decoded : FlatSem.valuesToString source = some result) :
    ∃ chunks : List (List HolChar), target = chunks.map ClosSem.Value.byteVector ∧
      result.explode = chunks.flatten := by
  induction related generalizing result with
  | nil =>
    simp [FlatSem.valuesToString] at decoded
    subst result
    exact ⟨[], rfl, by simp [ofString, MlString.explode]⟩
  | cons head tail ih =>
    cases head <;> simp [FlatSem.valuesToString] at decoded
    case string value =>
      rename_i sourceTail targetTail
      cases tailDecoded : FlatSem.valuesToString sourceTail with
      | none => simp [tailDecoded] at decoded
      | some rest =>
        simp [tailDecoded] at decoded
        subst result
        obtain ⟨chunks, targetEq, bytesEq⟩ := ih rest tailDecoded
        refine ⟨value.explode :: chunks, ?_, ?_⟩
        · simp [targetEq]
        · cases value
          cases rest
          simp_all [MlString.concat, MlString.explode]

end Flapjack.Compiler.Backend.FlatToClos
