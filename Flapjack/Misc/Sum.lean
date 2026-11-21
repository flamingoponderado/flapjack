module

public import Flapjack.HolRef

@[expose] public section

/-! HOL's sum-type discriminator and projections. -/
namespace Flapjack

/-- HOL `ISL`: the value is a left injection. -/
@[hol "HOL/src/coretypes/sumScript.sml" "ISL"]
def holIsl {α β : Type} : α ⊕ β → Prop
  | .inl _ => True
  | .inr _ => False

/-- The unspecified result of HOL `OUTL` on a right injection; HOL constrains
`OUTL` only on left injections. -/
noncomputable opaque holOutlInr (α : Type) {β : Type} [Nonempty α] : β → α

/-- The unspecified result of HOL `OUTR` on a left injection. -/
noncomputable opaque holOutrInl {α : Type} (β : Type) [Nonempty β] : α → β

/-- HOL `OUTL`, with its unconstrained value on right injections. -/
@[hol "HOL/src/coretypes/sumScript.sml" "OUTL" (total_function_inhabitants := [α])]
noncomputable def holOutl {α β : Type} [Nonempty α] : α ⊕ β → α
  | .inl x => x
  | .inr y => holOutlInr α y

/-- HOL `OUTR`, with its unconstrained value on left injections. -/
@[hol "HOL/src/coretypes/sumScript.sml" "OUTR" (total_function_inhabitants := [β])]
noncomputable def holOutr {α β : Type} [Nonempty β] : α ⊕ β → β
  | .inl x => holOutrInl β x
  | .inr y => y

end Flapjack
