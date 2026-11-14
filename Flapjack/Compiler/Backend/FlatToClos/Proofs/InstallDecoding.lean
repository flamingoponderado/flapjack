module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval

@[expose] public section

/-! Installation payload decoding across the proof-side value relation. -/
namespace Flapjack.Compiler.Backend.FlatToClos

/-- Related flat and closure values decode to the same installation bytes. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "v_rel_to_bytes"]
theorem installBytes_related (source : FlatSem.Value) (target : ClosSem.Value)
    (bytes : List (BitVec 8))
    (premises : ValueRel source target ∧ FlatSem.valueToBytes source = some bytes) :
    ClosSem.valueToBytes target = some bytes := by
  obtain ⟨related, decoded⟩ := premises
  have listDecoded := (FlatSem.valueToBytes_eq_some source bytes).1 decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_related source target _ related listDecoded
  apply (ClosSem.valueToBytes_eq_some target bytes).2
  have same : values = bytes.map (fun byte => ClosSem.Value.number byte.toNat) := by
    clear decoded listDecoded targetDecoded
    induction bytes generalizing values with
    | nil =>
      cases valuesRelated
      rfl
    | cons byte rest ih =>
      cases valuesRelated with
      | cons head tail =>
        cases head
        simp [ih _ tail]
  simpa [same] using targetDecoded

/-- Related flat and closure values decode to the same installation words. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "v_rel_to_words"]
theorem installWords_related (source : FlatSem.Value) (target : ClosSem.Value)
    (words : List (BitVec 64))
    (premises : ValueRel source target ∧ FlatSem.valueToWords source = some words) :
    ClosSem.valueToWords target = some words := by
  obtain ⟨related, decoded⟩ := premises
  have listDecoded := (FlatSem.valueToWords_eq_some source words).1 decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_related source target _ related listDecoded
  apply (ClosSem.valueToWords_eq_some target words).2
  have same : values = words.map ClosSem.Value.word64 := by
    clear decoded listDecoded targetDecoded
    induction words generalizing values with
    | nil =>
      cases valuesRelated
      rfl
    | cons word rest ih =>
      cases valuesRelated with
      | cons head tail =>
        cases head
        simp [ih _ tail]
  simpa [same] using targetDecoded

end Flapjack.Compiler.Backend.FlatToClos
