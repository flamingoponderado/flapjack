import Flapjack.HolRef

/-! Counterpart for the pinned original HOL optionScript.sml. -/
namespace Flapjack

open Classical in
/-- HOL `some P = if ?x. P x then SOME (@x. P x) else NONE`
    (`optionScript.sml:794-796`); under the guard, `Classical.choose` is a
    witness of `P` as HOL's `@x. P x`. This is a definition-shape port:
    arbitrary choices among multiple witnesses are unspecified in both logics;
    no cross-assistant equality of such choices is asserted. -/
@[hol "hol4/src/coretypes/optionScript.sml" "some_def"]
noncomputable def holOptionSome {α : Type} (P : α → Prop) : Option α :=
  if h : ∃ x, P x then some (Classical.choose h) else none

/-- Flapjack consequence of the guarded choice definition: selected values satisfy the predicate. -/
theorem holOptionSome_some {α : Type} {P : α → Prop} {x : α}
    (h : holOptionSome P = some x) : P x := by
  unfold holOptionSome at h
  split at h
  · rename_i hex; cases h; exact Classical.choose_spec hex
  · cases h

/-- Flapjack consequence of the guarded choice definition: NONE means no witness exists. -/
theorem holOptionSome_none {α : Type} {P : α → Prop}
    (h : holOptionSome P = none) : ∀ x, ¬ P x := by
  unfold holOptionSome at h
  split at h
  · cases h
  · rename_i hn; exact fun x hx => hn ⟨x, hx⟩

/-- HOL's value of `THE NONE`. `THE_DEF` (`optionScript.sml:176-180`) is a
`new_recursive_definition` with only the `SOME` clause, so HOL proves nothing
about `THE NONE`. An `opaque` constant is likewise a fixed value that no Lean
proof can unfold. The `Nonempty` binder is the inhabitedness every HOL type
has; it carries no other information. -/
noncomputable opaque holTheNone (α : Type) [Nonempty α] : α

/-- HOL `THE`: `THE (SOME x) = x`, with `THE NONE` the unspecified
`holTheNone`. -/
@[hol "hol4/src/coretypes/optionScript.sml" "THE_DEF"]
noncomputable def holThe {α : Type} [Nonempty α] : Option α → α
  | some x => x
  | none => holTheNone α

end Flapjack
