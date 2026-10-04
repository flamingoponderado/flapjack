import Flapjack.HolRef

/-! `miscScript.sml` `DISJOINT_INTER`. Sets are predicates, as in the reviewed
set_sep port: HOL `DISJOINT s t` is pointwise non-overlap and `∩` is pointwise
conjunction. -/
namespace Flapjack.Misc.DisjointInter

/-- Full original `DISJOINT_INTER`: `DISJOINT b c ⇒ DISJOINT (a ∩ b) (a ∩ c)`,
for an arbitrary element type. -/
@[hol "cakeml/misc/miscScript.sml" "DISJOINT_INTER"]
theorem disjointInter {α : Type} {a b c : α → Prop} (h : ∀ x, ¬ (b x ∧ c x)) :
    ∀ x, ¬ ((a x ∧ b x) ∧ (a x ∧ c x)) :=
  fun x ⟨⟨_, hb⟩, ⟨_, hc⟩⟩ => h x ⟨hb, hc⟩

end Flapjack.Misc.DisjointInter
