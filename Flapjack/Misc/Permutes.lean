module

public import Flapjack.Misc.PredSet
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# HOL `pred_set` `PERMUTES`

Counterpart of `pred_setScript.sml`'s `PERMUTES`. Sets are predicates, and
`PERMUTES` is rendered through the tagged `holBij`. The `Set` import lives here
rather than in `Flapjack.Misc.PredSet`: adding it there changes the simp set
seen by `Flapjack.Misc.StrongOrder` users and closes an unrelated proof early.
-/

namespace Flapjack

/-- Exact HOL `PERMUTES` (`pred_setScript.sml`): `f PERMUTES s = BIJ f s s`. -/
@[hol "HOL/src/pred_set/src/pred_setScript.sml" "PERMUTES"]
def holPermutes {α : Type} (f : α → α) (s : α → Prop) : Prop := holBij f s s

/-- Original `I_PERMUTES`: the identity permutes every set. -/
@[hol "cakeml/misc/miscScript.sml" "I_PERMUTES"]
theorem holPermutes_id {α : Type} (s : Set α) : holPermutes id s := by
  unfold holPermutes holBij holInj holSurj
  refine ⟨⟨fun x h => h, fun x y _ heq => heq⟩, ⟨fun x h => h, ?_⟩⟩
  intro x hx
  exact ⟨x, hx, rfl⟩

end Flapjack
