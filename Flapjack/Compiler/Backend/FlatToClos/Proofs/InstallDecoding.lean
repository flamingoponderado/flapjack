import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval

/-! Installation payload decoding across the proof-side value relation. -/
namespace Flapjack.Compiler.Backend.FlatToClos

private theorem byteList_related (bytes : List (BitVec 8)) (target : List ClosSem.Value)
    (related : List.Forall₂ ValueRel (bytes.map (FlatSem.Value.litv ∘ Flapjack.AstHOL.Lit.word8)) target) :
    target = bytes.map (fun byte => ClosSem.Value.number byte.toNat) := by
  induction bytes generalizing target with
  | nil => cases related; rfl
  | cons byte bytes ih =>
    cases related with
    | cons head tail =>
      cases head
      simp [ih _ tail]

private theorem wordList_related (words : List (BitVec 64)) (target : List ClosSem.Value)
    (related : List.Forall₂ ValueRel (words.map (FlatSem.Value.litv ∘ Flapjack.AstHOL.Lit.word64)) target) :
    target = words.map ClosSem.Value.word64 := by
  induction words generalizing target with
  | nil => cases related; rfl
  | cons word words ih =>
    cases related with
    | cons head tail =>
      cases head
      simp [ih _ tail]

/-- Related flat and closure values decode to the same installation bytes. -/
theorem installBytes_related (source : FlatSem.Value) (target : ClosSem.Value)
    (related : ValueRel source target) (bytes : List (BitVec 8))
    (decoded : FlatSem.valueToBytes source = some bytes) :
    ClosSem.valueToBytes target = some bytes := by
  have listDecoded := (FlatSem.valueToBytes_eq_some source bytes).1 decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_related source target _ related listDecoded
  apply (ClosSem.valueToBytes_eq_some target bytes).2
  simpa [byteList_related bytes values valuesRelated] using targetDecoded

/-- Related flat and closure values decode to the same installation words. -/
theorem installWords_related (source : FlatSem.Value) (target : ClosSem.Value)
    (related : ValueRel source target) (words : List (BitVec 64))
    (decoded : FlatSem.valueToWords source = some words) :
    ClosSem.valueToWords target = some words := by
  have listDecoded := (FlatSem.valueToWords_eq_some source words).1 decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_related source target _ related listDecoded
  apply (ClosSem.valueToWords_eq_some target words).2
  simpa [wordList_related words values valuesRelated] using targetDecoded

end Flapjack.Compiler.Backend.FlatToClos
