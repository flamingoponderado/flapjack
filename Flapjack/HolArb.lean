/-! Shared unspecified values for HOL pattern completion.
This untagged representation infrastructure uses one opaque value per inhabited
carrier, rather than a fresh value for each missing clause or argument. -/
namespace Flapjack
noncomputable opaque holArb (α : Type) [Nonempty α] : α
end Flapjack
