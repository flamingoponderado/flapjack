import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions

/-! Value decoding needed by the dynamic-installation simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- A source byte list and a related target value decode to identical bytes. -/
theorem install_valueToBytes_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (bytes : List (BitVec 8))
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.valueToBytes source = some bytes) :
    BvlSem.valueToBytes target = some bytes := by
  have sourceList := (ClosSem.valueToBytes_eq_some source bytes).1 decoded
  obtain ⟨values, targetList, valuesRel⟩ := decodedList_related source target _ related sourceList
  have valuesEq : values = bytes.map (fun b => BvlSem.Value.number b.toNat) := by
    clear decoded sourceList targetList related
    induction bytes generalizing values with
    | nil => cases valuesRel; rfl
    | cons byte rest ih =>
      cases valuesRel with
      | cons head tail =>
        have first := vRel_number_inv head
        have remaining := ih _ tail
        simp [first, remaining]
  apply (BvlSem.valueToBytes_eq_some target bytes).2
  simpa [valuesEq] using targetList

/-- A source word list and a related target value decode to identical words. -/
theorem install_valueToWords_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (words : List (BitVec 64))
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.valueToWords source = some words) :
    BvlSem.valueToWords target = some words := by
  have sourceList := (ClosSem.valueToWords_eq_some source words).1 decoded
  obtain ⟨values, targetList, valuesRel⟩ := decodedList_related source target _ related sourceList
  have valuesEq : values = words.map BvlSem.Value.word64 := by
    clear decoded sourceList targetList related
    induction words generalizing values with
    | nil => cases valuesRel; rfl
    | cons word rest ih =>
      cases valuesRel with
      | cons head tail =>
        have first := vRel_word64_inv head
        have remaining := ih _ tail
        simp [first, remaining]
  apply (BvlSem.valueToWords_eq_some target words).2
  simpa [valuesEq] using targetList

end Flapjack.Compiler.Backend.ClosToBvl
