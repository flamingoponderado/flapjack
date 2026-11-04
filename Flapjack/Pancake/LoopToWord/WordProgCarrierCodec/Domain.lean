import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-! Flapjack-only support for the actual partial production carrier encoder.
The structural domain is proved equal to the real encoder for every program.
These helpers describe codec acceptance, not HOL semantics or pass simulation,
and have no HOL original or HOL tags. -/

namespace Flapjack.WordProgCarrierCodec

/-- Flapjack-only Option-domain packaging, with no separate HOL original. -/
theorem optionPairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

/-- Flapjack-only single-payload Option-domain packaging. -/
theorem optionMapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

end Flapjack.WordProgCarrierCodec
