import Flapjack.Misc.Option

/-!
# HOL `pred_set` `LINV`

Counterpart for the left-inverse group of the pinned original HOL
`src/pred_set/src/pred_setScript.sml` (lines 2715-2779). Sets are predicates, `y IN IMAGE f s`
is `∃ x, y = f x ∧ s x` (HOL `IN_IMAGE`), and `UNIV` is `fun _ => True`.
-/

namespace Flapjack

open Classical in
/-- HOL `LINV_OPT_def` (`pred_setScript.sml:2715-2718`, `[nocompute]`):
`LINV_OPT f s y = if y IN IMAGE f s then SOME (@x. x IN s /\ (f x = y)) else NONE`. Under the
guard, `Classical.choose` is a witness of `x IN s /\ f x = y`, as HOL's `@`. This is a
definition-shape port: arbitrary choices among several witnesses are unspecified in both
logics, and no cross-assistant equality of such choices is asserted. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "LINV_OPT_def"]
noncomputable def holLinvOpt {α β : Type} (f : α → β) (s : α → Prop) (y : β) : Option α :=
  if h : ∃ x, y = f x ∧ s x then
    some (Classical.choose (show ∃ x, s x ∧ f x = y from
      let ⟨x, h1, h2⟩ := h; ⟨x, h2, h1.symm⟩))
  else none

/-- HOL `LINV_LO` (`pred_setScript.sml:2776-2778`, `[nocompute]`):
`LINV f s y = THE (LINV_OPT f s y)`, with `THE` the reviewed `holThe` (whose `THE NONE` is
unspecified). The `Nonempty` binder is the inhabitedness every HOL type has. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "LINV_LO"]
noncomputable def holLinv {α β : Type} [Nonempty α] (f : α → β) (s : α → Prop) (y : β) : α :=
  holThe (holLinvOpt f s y)

/-- `LINV_DEF` on `UNIV` for an injective `f` (Flapjack infrastructure; HOL's theorem takes
`INJ f s t`). -/
theorem holLinv_apply_of_injective {α β : Type} [Nonempty α] {f : α → β}
    (hf : Function.Injective f) (x : α) : holLinv f (fun _ => True) (f x) = x := by
  have h : ∃ z, f x = f z ∧ (fun _ => True) z := ⟨x, rfl, trivial⟩
  simp only [holLinv, holLinvOpt, dif_pos h, holThe]
  exact hf (Classical.choose_spec (show ∃ z, (fun _ => True) z ∧ f z = f x from
    let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1.symm⟩)).2

/-- `BIJ_LINV_INV` on `UNIV` for a surjective `f` (Flapjack infrastructure; HOL's theorem takes
`BIJ f s t`). -/
theorem apply_holLinv_of_surjective {α β : Type} [Nonempty α] {f : α → β}
    (hf : Function.Surjective f) (y : β) : f (holLinv f (fun _ => True) y) = y := by
  obtain ⟨x, rfl⟩ := hf y
  have h : ∃ z, f x = f z ∧ (fun _ => True) z := ⟨x, rfl, trivial⟩
  simp only [holLinv, holLinvOpt, dif_pos h, holThe]
  exact (Classical.choose_spec (show ∃ z, (fun _ => True) z ∧ f z = f x from
    let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1.symm⟩)).2

end Flapjack
