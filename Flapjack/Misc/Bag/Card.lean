module

public import Flapjack.Misc.Bag

@[expose] public section

/-! HOL's inductively defined bag-cardinality relation. -/
namespace Flapjack

/-- The bag can be built from the empty bag using exactly `n` insertions. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_CARD_RELn"]
def bagCardRel {α : Type} (b : Bag α) (n : Nat) : Prop :=
  ∀ P : Bag α → Nat → Prop,
    P emptyBag 0 ∧ (∀ b n, P b n → ∀ e, P (bagInsert e b) (n + 1)) → P b n


/-- Flapjack infrastructure: finite bags admit a cardinality-relation witness. -/
private theorem relExists {α : Type} (b : Bag α) (finite : finiteBag b) :
    ∃ n, bagCardRel b n := by
  apply finite (fun b => ∃ n, bagCardRel b n)
  constructor
  · refine ⟨0, ?_⟩
    intro P h
    exact h.1
  · intro b ⟨n, hn⟩ e
    refine ⟨n + 1, ?_⟩
    intro P h
    exact h.2 b n (hn P h) e

/-- Flapjack infrastructure: a total function satisfying the HOL specification exists. -/
theorem holBagCardExists {α : Type} :
    ∃ f : Bag α → Nat, ∀ b, finiteBag b → bagCardRel b (f b) := by
  classical
  have hex (b : Bag α) : ∃ n, finiteBag b → bagCardRel b n := by
    by_cases h : finiteBag b
    · obtain ⟨n, hn⟩ := relExists b h
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun hf => False.elim (h hf)⟩
  exact ⟨fun b => Classical.choose (hex b), fun b => Classical.choose_spec (hex b)⟩

/-- The HOL specified cardinality function; infinite bags are unconstrained. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_CARD"]
noncomputable def holBagCard {α : Type} : Bag α → Nat := Classical.choose (holBagCardExists (α := α))

/-- The specification that defines HOL bag cardinality. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_CARD"]
theorem holBagCard_spec {α : Type} : ∀ b : Bag α, finiteBag b → bagCardRel b (holBagCard b) :=
  Classical.choose_spec (holBagCardExists (α := α))


end Flapjack
