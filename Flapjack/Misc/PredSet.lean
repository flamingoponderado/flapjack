module

public import Flapjack.Misc.Option

@[expose] public section

/-!
# HOL `pred_set` `LINV`

Counterpart for the left-inverse group of the pinned original HOL
`src/pred_set/src/pred_setScript.sml` (lines 2715-2779). Sets are predicates, `y IN IMAGE f s`
is `∃ x, y = f x ∧ s x` (HOL `IN_IMAGE`), and `UNIV` is `fun _ => True`.
-/

namespace Flapjack

/-- HOL's injectivity relation between two sets. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "INJ_DEF"]
def holInj {α β : Type} (f : α → β) (s : α → Prop) (t : β → Prop) : Prop :=
  (∀ x, s x → t (f x)) ∧ (∀ x y, s x ∧ s y → f x = f y → x = y)

/-- HOL's surjectivity relation between two sets. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "SURJ_DEF"]
def holSurj {α β : Type} (f : α → β) (s : α → Prop) (t : β → Prop) : Prop :=
  (∀ x, s x → t (f x)) ∧ (∀ x, t x → ∃ y, s y ∧ f y = x)

/-- HOL's bijectivity relation between two sets: injective and surjective. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_DEF"]
def holBij {α β : Type} (f : α → β) (s : α → Prop) (t : β → Prop) : Prop :=
  holInj f s t ∧ holSurj f s t

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
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "LINV_LO"
  (total_function_inhabitants := [α])]
noncomputable def holLinv {α β : Type} [Nonempty α] (f : α → β) (s : α → Prop) (y : β) : α :=
  holThe (holLinvOpt f s y)

/-- The optional inverse identifies exactly the domain elements of an injection. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "INJ_LINV_OPT"]
theorem holInjLinvOpt {α β : Type} (f : α → β) (s : α → Prop) (t : β → Prop) :
    holInj f s t → ∀ x y, holLinvOpt f s y = some x ↔ y = f x ∧ s x ∧ t y := by
  intro inj x y
  classical
  constructor
  · intro found
    unfold holLinvOpt at found
    split at found
    next h =>
      have spec := Classical.choose_spec (show ∃ z, s z ∧ f z = y from
        let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1.symm⟩)
      have equal := Option.some.inj found
      rw [equal] at spec
      exact ⟨spec.2.symm, spec.1, spec.2 ▸ inj.1 x spec.1⟩
    next h => contradiction
  · rintro ⟨rfl, hx, _⟩
    have h : ∃ z, f x = f z ∧ s z := ⟨x, rfl, hx⟩
    simp only [holLinvOpt, dif_pos h, Option.some.injEq]
    have spec := Classical.choose_spec (show ∃ z, s z ∧ f z = f x from
      let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1.symm⟩)
    exact inj.2 _ x ⟨spec.1, hx⟩ spec.2

/-- An injective map's left inverse recovers every member of its domain. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "LINV_DEF"]
theorem holLinvDef {α β : Type} [Nonempty α] (f : α → β) (s : α → Prop) (t : β → Prop) :
    holInj f s t → ∀ x, s x → holLinv f s (f x) = x := by
  intro hf x hx
  have h : ∃ z, f x = f z ∧ s z := ⟨x, rfl, hx⟩
  simp only [holLinv, holLinvOpt, dif_pos h, holThe]
  have chosen := Classical.choose_spec (show ∃ z, s z ∧ f z = f x from
    let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1.symm⟩)
  exact hf.2 _ x ⟨chosen.1, hx⟩ chosen.2

/-- `BIJ_LINV_INV` on `UNIV` for a surjective `f` (Flapjack infrastructure; HOL's theorem takes
`BIJ f s t`). -/
theorem apply_holLinv_of_surjective {α β : Type} [Nonempty α] {f : α → β}
    (hf : Function.Surjective f) (y : β) : f (holLinv f (fun _ => True) y) = y := by
  obtain ⟨x, rfl⟩ := hf y
  have h : ∃ z, f x = f z ∧ (fun _ => True) z := ⟨x, rfl, trivial⟩
  simp only [holLinv, holLinvOpt, dif_pos h, holThe]
  exact (Classical.choose_spec (show ∃ z, (fun _ => True) z ∧ f z = f x from
    let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1.symm⟩)).2

/-- Original `INJ_I`: the identity is injective into exactly the supersets.
    HOL's set carrier `α -> bool` is the predicate `α → Prop`, so `s ⊆ t` is the
    pointwise implication. -/
@[hol "cakeml/misc/miscScript.sml" "INJ_I"]
theorem inj_id_iff_subset {α : Type} (s t : α → Prop) :
    holInj id s t ↔ ∀ x, s x → t x := by
  constructor
  · intro h x hx
    exact h.1 x hx
  · intro h
    refine ⟨fun x hx => h x hx, ?_⟩
    intro x y _ heq
    simpa using heq

end Flapjack
