import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ListConversion
import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval

/-! Byte and word list decoding across the factored source-to-flat value
relation. The underlying relation is still awaiting HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

private theorem maybeAllList_shape {α β : Type} (decode : α → Option β) (encode : β → α)
    (recover : ∀ x y, decode x = some y → x = encode y) :
    ∀ xs ys, maybeAllList (xs.map decode) = some ys → xs = ys.map encode := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp [maybeAllList] at h
    subst ys
    rfl
  | cons head tail ih =>
    intro ys h
    cases headResult : decode head with
    | none => simp [maybeAllList, headResult] at h
    | some value =>
      cases tailResult : maybeAllList (tail.map decode) with
      | none => simp [maybeAllList, headResult, tailResult] at h
      | some values =>
        simp [maybeAllList, headResult, tailResult] at h
        subst ys
        simp [recover head value headResult, ih values tailResult]

private theorem related_literals (genv : GlobalEnv) (lits : List Lit) (flat : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel genv) (lits.map Value.litv) flat) :
    flat = lits.map FlatSem.Value.litv := by
  induction lits generalizing flat with
  | nil => cases related; rfl
  | cons lit lits ih =>
    cases related with
    | cons head tail =>
      have same := (valueRel_literal_iff genv lit _).mp head
      simp [same, ih _ tail]

private theorem word8_recover (value : Value) (byte : BitVec 8)
    (decoded : valueToWord8 value = some byte) : value = .litv (.word8 byte) := by
  cases value <;> try (simp [valueToWord8] at decoded)
  case litv lit => cases lit <;> simp_all

private theorem word64_recover (value : Value) (word : BitVec 64)
    (decoded : valueToWord64 value = some word) : value = .litv (.word64 word) := by
  cases value <;> try (simp [valueToWord64] at decoded)
  case litv lit => cases lit <;> simp_all

/-- Successful source byte-list decoding is preserved by related flat values.
This is a factored counterpart of the original proof obligation. -/
theorem valueToWord8List_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : Value) (flat : FlatSem.Value) (bytes : List (BitVec 8))
    (decoded : valueToWord8List source = some bytes) (related : ValueRel genv source flat) :
    FlatSem.valueToBytes flat = some bytes := by
  cases sourceList : valueToList source with
  | none => simp [valueToWord8List, sourceList] at decoded
  | some values =>
    have decodedList : maybeAllList (values.map valueToWord8) = some bytes := by
      simpa [valueToWord8List, sourceList] using decoded
    have shape := maybeAllList_shape valueToWord8 (fun b => Value.litv (.word8 b)) word8_recover values bytes decodedList
    obtain ⟨flatValues, flatDecoded, listRel⟩ := valueToList_related genv ok source flat values related sourceList
    rw [shape] at listRel
    have flatShape : flatValues = bytes.map (FlatSem.Value.litv ∘ Lit.word8) := by
      simpa [List.map_map, Function.comp_def] using related_literals genv (bytes.map Lit.word8) flatValues
        (by simpa [List.map_map, Function.comp_def] using listRel)
    apply (FlatSem.valueToBytes_eq_some flat bytes).mpr
    simpa [flatShape] using flatDecoded

/-- Successful source 64-bit word-list decoding is preserved by related flat
values. This is a factored counterpart of the original proof obligation. -/
theorem valueToWord64List_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : Value) (flat : FlatSem.Value) (words : List (BitVec 64))
    (decoded : valueToWord64List source = some words) (related : ValueRel genv source flat) :
    FlatSem.valueToWords flat = some words := by
  cases sourceList : valueToList source with
  | none => simp [valueToWord64List, sourceList] at decoded
  | some values =>
    have decodedList : maybeAllList (values.map valueToWord64) = some words := by
      simpa [valueToWord64List, sourceList] using decoded
    have shape := maybeAllList_shape valueToWord64 (fun w => Value.litv (.word64 w)) word64_recover values words decodedList
    obtain ⟨flatValues, flatDecoded, listRel⟩ := valueToList_related genv ok source flat values related sourceList
    rw [shape] at listRel
    have flatShape : flatValues = words.map (FlatSem.Value.litv ∘ Lit.word64) := by
      simpa [List.map_map, Function.comp_def] using related_literals genv (words.map Lit.word64) flatValues
        (by simpa [List.map_map, Function.comp_def] using listRel)
    apply (FlatSem.valueToWords_eq_some flat words).mpr
    simpa [flatShape] using flatDecoded

end Flapjack.Compiler.Backend.SourceToFlat
