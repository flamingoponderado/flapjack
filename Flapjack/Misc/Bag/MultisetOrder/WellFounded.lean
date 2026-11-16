module

public import Flapjack.Misc.Bag.MultisetOrder
public import Flapjack.Misc.Bag.SubBag
import Mathlib.Data.Multiset.DershowitzManna

@[expose] public section

/-! Well-foundedness of HOL's finite-bag multiset ordering. -/
namespace Flapjack

private noncomputable def multisetCount {α : Type} (m : Multiset α) : Bag α :=
  fun x => @Multiset.count α (Classical.decEq α) x m

private theorem finiteBagHasMultiset {α : Type} (b : Bag α) (h : finiteBag b) :
    ∃ m : Multiset α, multisetCount m = b := by
  classical
  apply h (fun b => ∃ m : Multiset α, multisetCount m = b)
  constructor
  · refine ⟨0, ?_⟩
    funext x
    simp [multisetCount, emptyBag]
  · intro b ⟨m, hm⟩ e
    refine ⟨e ::ₘ m, ?_⟩
    funext x
    have hx := congrFun hm x
    change Multiset.count x m = b x at hx
    by_cases he : x = e
    · subst x
      simp [multisetCount, bagInsert, hx]
    · simp [multisetCount, bagInsert, he, hx]

private noncomputable def finiteBagMultiset {α : Type} (b : Bag α) : Multiset α := by
  classical
  exact if h : finiteBag b then Classical.choose (finiteBagHasMultiset b h) else 0

private theorem finiteBagMultisetCount {α : Type} (b : Bag α) (h : finiteBag b) :
    multisetCount (finiteBagMultiset b) = b := by
  classical
  simp only [finiteBagMultiset, dif_pos h]
  exact Classical.choose_spec (finiteBagHasMultiset b h)

private theorem finiteBagMultisetCountAt {α : Type} (b : Bag α) (h : finiteBag b) (x : α) :
    @Multiset.count α (Classical.decEq α) x (finiteBagMultiset b) = b x :=
  congrFun (finiteBagMultisetCount b h) x

@[hol "HOL/src/bag/bagScript.sml" "WF_mlt1"]
theorem wfBagMultisetStep {α : Type} (r : α → α → Prop) (hr : WellFounded r) :
    WellFounded (bagMultisetStep r) := by
  classical
  have ht : WellFounded (Relation.TransGen r) := hr.transGen
  have noSelf : ∀ a, ¬ Relation.TransGen r a a := by
    intro a
    induction a using ht.induction with
    | h a ih =>
      intro h
      exact ih a h h
  let : Preorder α := {
    le := Relation.ReflTransGen r
    lt := Relation.TransGen r
    le_refl := fun _ => .refl
    le_trans := fun _ _ _ => Relation.ReflTransGen.trans
    lt_iff_le_not_ge := by
      intro a b
      constructor
      · intro h
        refine ⟨h.to_reflTransGen, ?_⟩
        intro back
        exact noSelf a (h.trans_left back)
      · rintro ⟨forward, notBack⟩
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp forward with eq | path
        · subst b
          exact (notBack .refl).elim
        · exact path }
  let : WellFoundedLT α := ⟨ht⟩
  apply Subrelation.wf _ (InvImage.wf finiteBagMultiset Multiset.wellFounded_isDershowitzMannaLT)
  intro left right h
  obtain ⟨hl, hr', e, rep, res, eqLeft, eqRight, related⟩ := h
  have hparts : finiteBag rep ∧ finiteBag res :=
    (finiteBagUnionIff rep res).mp (eqLeft ▸ hl)
  refine ⟨finiteBagMultiset res, finiteBagMultiset rep, {e}, by simp, ?_, ?_, ?_⟩
  · apply Multiset.ext'
    intro x
    simp only [Multiset.count_add, finiteBagMultisetCountAt _ hl,
      finiteBagMultisetCountAt _ hparts.1, finiteBagMultisetCountAt _ hparts.2]
    have eq := congrFun eqLeft x
    simp only [bagUnion] at eq
    omega
  · apply Multiset.ext'
    intro x
    simp only [Multiset.count_add, finiteBagMultisetCountAt _ hr',
      finiteBagMultisetCountAt _ hparts.2]
    have eq := congrFun eqRight x
    by_cases hx : x = e <;> simp [bagUnion, bagInsert, emptyBag, hx] at eq ⊢ <;> omega
  · intro y hy
    have hypos : 0 < Multiset.count y (finiteBagMultiset rep) := Multiset.count_pos.mpr hy
    rw [finiteBagMultisetCountAt rep hparts.1 y] at hypos
    have mem : bagIn y rep := by
      change 1 ≤ rep y
      omega
    exact ⟨e, by simp, Relation.TransGen.single (related y mem)⟩

end Flapjack
