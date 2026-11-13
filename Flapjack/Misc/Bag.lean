module

public import Flapjack.HolRef

@[expose] public section

/-! The polymorphic HOL bag carrier and basic union laws. -/
namespace Flapjack

/-- HOL bags are functions from elements to natural multiplicities. -/
@[hol "HOL/src/bag/bagScript.sml" "bag"]
abbrev Bag (α : Type) := α → Nat

/-- Membership of an element with at least a given multiplicity. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_INN"]
def bagInn {α : Type} (e : α) (n : Nat) (b : Bag α) : Prop := n ≤ b e

/-- Every multiplicity in the first bag is present in the second. -/
@[hol "HOL/src/bag/bagScript.sml" "SUB_BAG"]
def subBag {α : Type} (b₁ b₂ : Bag α) : Prop :=
  ∀ x n, bagInn x n b₁ → bagInn x n b₂

/-- An element belongs to a bag when its multiplicity is at least one. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_IN"]
def bagIn {α : Type} (e : α) (b : Bag α) : Prop := bagInn e 1 b

/-- The set of elements occurring in a bag. -/
@[hol "HOL/src/bag/bagScript.sml" "SET_OF_BAG"]
def setOfBag {α : Type} (b : Bag α) : α → Prop := fun x => bagIn x b

/-- Turn a set predicate into its characteristic bag. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_OF_SET"]
noncomputable def bagOfSet {α : Type} (P : α → Prop) : Bag α := by
  classical
  exact fun x => if P x then 1 else 0

/-- Every element has multiplicity at most one. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_ALL_DISTINCT"]
def bagAllDistinct {α : Type} (b : Bag α) : Prop := ∀ e, b e ≤ 1

/-- A sub-bag of an all-distinct bag is all-distinct. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_ALL_DISTINCT_SUB_BAG"]
theorem bagAllDistinct_subBag {α : Type} (s t : Bag α)
    (premises : subBag s t ∧ bagAllDistinct t) : bagAllDistinct s := by
  intro e
  exact Nat.le_trans (premises.1 e (s e) (Nat.le_refl _)) (premises.2 e)

/-- The constant-zero bag. -/
@[hol "HOL/src/bag/bagScript.sml" "EMPTY_BAG"]
def emptyBag {α : Type} : Bag α := fun _ => 0

/-- Bag union adds multiplicities pointwise. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_UNION"]
def bagUnion {α : Type} (left right : Bag α) : Bag α := fun x => left x + right x

/-- Insert one occurrence of an element into a HOL bag. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_INSERT"]
noncomputable def bagInsert {α : Type} (element : α) (bag : Bag α) : Bag α := by
  classical
  exact fun x => if x = element then bag element + 1 else bag x

/-- A finite bag belongs to every collection closed under insertion. -/
@[hol "HOL/src/bag/bagScript.sml" "FINITE_BAG"]
def finiteBag {α : Type} (bag : Bag α) : Prop :=
  ∀ P : Bag α → Prop, P emptyBag ∧ (∀ b, P b → ∀ e, P (bagInsert e b)) → P bag

/-- The empty bag is finite. -/
@[hol "HOL/src/bag/bagScript.sml" "FINITE_EMPTY_BAG"]
theorem finiteEmptyBag {α : Type} : finiteBag (emptyBag : Bag α) := by
  intro P h
  exact h.1

/-- Inserting an element preserves bag finiteness. -/
@[hol "HOL/src/bag/bagScript.sml" "FINITE_BAG_INSERT" 1262]
theorem finiteBagInsert {α : Type} (b : Bag α) (h : finiteBag b) :
    ∀ e, finiteBag (bagInsert e b) := by
  intro e P hP
  exact hP.2 b (h P hP) e

private theorem bagUnion_insert_left {α : Type} (e : α) (a b : Bag α) :
    bagUnion (bagInsert e a) b = bagInsert e (bagUnion a b) := by
  classical
  funext x
  by_cases h : x = e <;> simp [bagUnion, bagInsert, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The union of two finite bags is finite. -/
@[hol "HOL/src/bag/bagScript.sml" "FINITE_BAG_UNION_1"]
theorem finiteBagUnion {α : Type} (a : Bag α) (ha : finiteBag a)
    (b : Bag α) (hb : finiteBag b) : finiteBag (bagUnion a b) := by
  apply ha (fun x => finiteBag (bagUnion x b))
  constructor
  · have eq : bagUnion emptyBag b = b := by
      funext x
      simp [bagUnion, emptyBag]
    rw [eq]
    exact hb
  · intro x hx e
    rw [bagUnion_insert_left]
    exact finiteBagInsert _ hx e

/-- The two union identities and the characterization of empty unions.
The three conjuncts have independently quantified element types, as in HOL. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_UNION_EMPTY"]
theorem bagUnion_empty {α β γ : Type} :
    (∀ b : Bag α, bagUnion b emptyBag = b) ∧
    (∀ b : Bag β, bagUnion emptyBag b = b) ∧
    (∀ b₁ b₂ : Bag γ, bagUnion b₁ b₂ = emptyBag ↔ b₁ = emptyBag ∧ b₂ = emptyBag) := by
  simp [bagUnion, emptyBag, funext_iff, Nat.add_eq_zero_iff, forall_and]

/-- Projection of the right-identity conjunct for a single bag. -/
theorem bagUnion_empty_right {α : Type} (b : Bag α) : bagUnion b emptyBag = b :=
  (bagUnion_empty (α := α) (β := α) (γ := α)).1 b

/-- Projection of the left-identity conjunct for a single bag. -/
theorem bagUnion_empty_left {α : Type} (b : Bag α) : bagUnion emptyBag b = b :=
  (bagUnion_empty (α := α) (β := α) (γ := α)).2.1 b

end Flapjack
