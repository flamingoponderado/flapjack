module

public import Flapjack.HolRef
public import Flapjack.HolArb
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# HOL `pred_set` `CHOICE` and `REST`

Counterpart for the `CHOICE`/`REST` group of the pinned original HOL
`src/pred_set/src/pred_setScript.sml` (lines 1520-1550). HOL sets `'a -> bool`
are Mathlib `Set α`; `s DELETE x` is `s \ {x}` and `{}` is `∅`.

HOL introduces `CHOICE` by `new_specification ("CHOICE_DEF", ["CHOICE"],
CHOICE_EXISTS)`: only `s ≠ {} ⇒ CHOICE s ∈ s` is known, and `CHOICE {}` is
unspecified. The Lean rendering takes the element from the set's own
membership witness when the set is nonempty, and HOL's unspecified value
`holArb α` (from the reviewed `Nonempty α` inhabitant) otherwise. Any choice
among several members is unspecified in both logics; no cross-assistant
equality of such choices is asserted.
-/

namespace Flapjack

open Classical in
/-- HOL `CHOICE` (`pred_setScript.sml:1520-1530`, specified by `CHOICE_DEF`). -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "CHOICE_DEF"
  (total_function_inhabitants := [α])]
noncomputable def holChoice {α : Type} [Nonempty α] (s : Set α) : α :=
  if h : s.Nonempty then Classical.choose h else holArb α

/-- The specification `CHOICE_DEF` of HOL `CHOICE`: a nonempty set contains its
chosen element. Flapjack proof infrastructure for the tagged `holChoice`. -/
theorem holChoice_mem {α : Type} [Nonempty α] (s : Set α) (h : s ≠ ∅) : holChoice s ∈ s := by
  have hn : s.Nonempty := Set.nonempty_iff_ne_empty.mpr h
  simp only [holChoice, dif_pos hn]
  exact Classical.choose_spec hn

/-- HOL `REST_DEF` (`pred_setScript.sml:1544-1546`):
`REST s = s DELETE CHOICE s`. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "REST_DEF"
  (total_function_inhabitants := [α])]
noncomputable def holRest {α : Type} [Nonempty α] (s : Set α) : Set α :=
  s \ {holChoice s}

end Flapjack
