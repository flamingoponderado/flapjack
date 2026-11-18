module

public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Codec laws for the optional substitutions returned by the unifier. -/
namespace Flapjack.HOL.Unification

/-- Canonical finite maps survive conversion to the broad carrier and back. -/
private theorem finiteMapCodecRoundtrip {K V : Type} (map : HolFiniteMapExact K V) :
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad map) = map := by
  cases map
  rfl

/-- Broad finite maps survive the inverse carrier conversion. -/
private theorem finiteMapBroadCodecRoundtrip {K V : Type} (map : FiniteMapBroad K V) :
    FiniteMapBroad.toBroad (FiniteMapBroad.ofBroad map) = map := by
  cases map
  rfl

/-- Representation infrastructure for optional finite-map results: converting
    a result to the broad finite-support carrier and back preserves it. This
    is not a separate HOL declaration. -/
theorem optionSubstCodecRoundtrip {K V : Type}
    (result : Option (HolFiniteMapExact K V)) :
    (result.map FiniteMapBroad.toBroad).map FiniteMapBroad.ofBroad = result := by
  cases result with
  | none => rfl
  | some s => simp [finiteMapCodecRoundtrip]

/-- The reverse optional finite-map codec roundtrip. Together with
    `optionSubstCodecRoundtrip`, this records both directions of the carrier
    translation without excluding unsuccessful results. -/
theorem optionSubstBroadCodecRoundtrip {K V : Type}
    (result : Option (FiniteMapBroad K V)) :
    (result.map FiniteMapBroad.ofBroad).map FiniteMapBroad.toBroad = result := by
  cases result with
  | none => rfl
  | some s => simp [finiteMapBroadCodecRoundtrip]

/-- The optional broad view reflects equality, including the distinction
    between failure and a successful empty map. This representation lemma has
    no separate HOL original. -/
theorem optionSubstCodecInjective {K V : Type}
    (left right : Option (HolFiniteMapExact K V)) :
    left.map FiniteMapBroad.toBroad = right.map FiniteMapBroad.toBroad ↔ left = right := by
  constructor
  · intro h
    have mapped := congrArg (Option.map FiniteMapBroad.ofBroad) h
    simpa only [optionSubstCodecRoundtrip] using mapped
  · intro h
    rw [h]

end Flapjack.HOL.Unification
