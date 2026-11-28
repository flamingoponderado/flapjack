module

public import Flapjack.Misc.PredSet
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Insert

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

/-- Original `CARD_IMAGE_EQ_BIJ`: a finite set whose image has the same
cardinality is in bijection with that image. -/
@[hol "cakeml/misc/miscScript.sml" "CARD_IMAGE_EQ_BIJ"]
theorem cardImageEqBij {α β : Type} (s : Set α) (f : α → β) (hfin : s.Finite)
    (hcard : (f '' s).ncard = s.ncard) : holBij f s (f '' s) := by
  have hinj : Set.InjOn f s := Set.injOn_of_ncard_image_eq (hs := hfin) hcard
  unfold holBij holInj holSurj
  refine ⟨⟨fun x hx => ⟨x, hx, rfl⟩, fun x y hxy heq => hinj hxy.1 hxy.2 heq⟩,
    ⟨fun x hx => ⟨x, hx, rfl⟩, ?_⟩⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

/-- Original `CARD_IMAGE_ID_BIJ`: a self-mapping of a finite set with a
cardinality-preserving image permutes the set. -/
@[hol "cakeml/misc/miscScript.sml" "CARD_IMAGE_ID_BIJ"]
theorem cardImageIdBij {α : Type} (s : Set α) (f : α → α) (hfin : s.Finite)
    (h : (∀ x ∈ s, f x ∈ s) ∧ (f '' s).ncard = s.ncard) : holPermutes f s := by
  obtain ⟨hsub, hcard⟩ := h
  have himage : f '' s = s := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (ht := hfin)
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hsub x hx
    · omega
  unfold holPermutes
  have hbij := cardImageEqBij s f hfin hcard
  rw [himage] at hbij
  exact hbij

/-- Original `BIJ_UPDATE`: extending a bijection by one fresh pair keeps it a
bijection on the enlarged sets. -/
@[hol "cakeml/misc/miscScript.sml" "BIJ_UPDATE"]
theorem bijUpdate {α β : Type} [DecidableEq α] (f : α → β) (s : Set α) (t : Set β)
    (x : α) (y : β) (h : holBij f s t) (hx : x ∉ s) (hy : y ∉ t) :
    holBij (fun z => if z = x then y else f z) (insert x s : Set α) (insert y t : Set β) := by
  classical
  unfold holBij holInj holSurj at h ⊢
  obtain ⟨⟨hmap, hinj⟩, ⟨-, hsurj⟩⟩ := h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro z hz
    have hz' : z ∈ (insert x s : Set α) := hz
    rw [Set.mem_insert_iff] at hz'
    show (if z = x then y else f z) ∈ (insert y t : Set β)
    rw [Set.mem_insert_iff]
    by_cases h1 : z = x
    · exact Or.inl (by simp [h1])
    · simp only [if_neg h1]
      exact Or.inr (hmap z (hz'.resolve_left h1))
  · intro z1 z2 hz heq
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : z1 ∈ (insert x s : Set α) := hz1
    have hz2' : z2 ∈ (insert x s : Set α) := hz2
    rw [Set.mem_insert_iff] at hz1' hz2'
    by_cases h1 : z1 = x
    · subst z1
      by_cases h2 : z2 = x
      · exact h2.symm
      · have hval : f z2 = y := by
          have hcopy := heq
          simp only [if_neg h2, if_true] at hcopy
          exact hcopy.symm
        exact (hy (hval ▸ hmap _ (hz2'.resolve_left h2))).elim
    · by_cases h2 : z2 = x
      · subst z2
        have hval : f z1 = y := by
          have hcopy := heq
          simp only [if_neg h1, if_true] at hcopy
          exact hcopy
        exact (hy (hval ▸ hmap _ (hz1'.resolve_left h1))).elim
      · have hval : f z1 = f z2 := by
          have hcopy := heq
          simp only [if_neg h1, if_neg h2] at hcopy
          exact hcopy
        exact hinj _ _ ⟨hz1'.resolve_left h1, hz2'.resolve_left h2⟩ hval
  · intro z hz
    have hz' : z ∈ (insert x s : Set α) := hz
    rw [Set.mem_insert_iff] at hz'
    show (if z = x then y else f z) ∈ (insert y t : Set β)
    rw [Set.mem_insert_iff]
    by_cases h1 : z = x
    · exact Or.inl (by simp [h1])
    · simp only [if_neg h1]
      exact Or.inr (hmap z (hz'.resolve_left h1))
  · intro z hz
    have hz' : z ∈ (insert y t : Set β) := hz
    rw [Set.mem_insert_iff] at hz'
    rcases hz' with rfl | hz'
    · exact ⟨x, Set.mem_insert x s, by simp⟩
    · obtain ⟨z0, hz0, hz0eq⟩ := hsurj z hz'
      have hne : z0 ≠ x := by
        intro heq
        exact hx (heq ▸ hz0)
      refine ⟨z0, Set.mem_insert_of_mem x hz0, ?_⟩
      simp only [if_neg hne]
      exact hz0eq

/-- Original `INJ_UPDATE`: extending an injection by one fresh pair keeps it an
injection on the enlarged sets. -/
@[hol "cakeml/misc/miscScript.sml" "INJ_UPDATE"]
theorem injUpdate {α β : Type} [DecidableEq α] (f : α → β) (s : Set α) (t : Set β)
    (x : α) (y : β) (h : holInj f s t) (_hx : x ∉ s) (hy : y ∉ t) :
    holInj (fun z => if z = x then y else f z) (insert x s : Set α) (insert y t : Set β) := by
  classical
  unfold holInj at h ⊢
  obtain ⟨hmap, hinj⟩ := h
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz' : z ∈ (insert x s : Set α) := hz
    rw [Set.mem_insert_iff] at hz'
    show (if z = x then y else f z) ∈ (insert y t : Set β)
    rw [Set.mem_insert_iff]
    by_cases h1 : z = x
    · exact Or.inl (by simp [h1])
    · simp only [if_neg h1]
      exact Or.inr (hmap z (hz'.resolve_left h1))
  · intro z1 z2 hz heq
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : z1 ∈ (insert x s : Set α) := hz1
    have hz2' : z2 ∈ (insert x s : Set α) := hz2
    rw [Set.mem_insert_iff] at hz1' hz2'
    by_cases h1 : z1 = x
    · subst z1
      by_cases h2 : z2 = x
      · exact h2.symm
      · have hval : f z2 = y := by
          have hcopy := heq
          simp only [if_neg h2, if_true] at hcopy
          exact hcopy.symm
        exact (hy (hval ▸ hmap _ (hz2'.resolve_left h2))).elim
    · by_cases h2 : z2 = x
      · subst z2
        have hval : f z1 = y := by
          have hcopy := heq
          simp only [if_neg h1, if_true] at hcopy
          exact hcopy
        exact (hy (hval ▸ hmap _ (hz1'.resolve_left h1))).elim
      · have hval : f z1 = f z2 := by
          have hcopy := heq
          simp only [if_neg h1, if_neg h2] at hcopy
          exact hcopy
        exact hinj _ _ ⟨hz1'.resolve_left h1, hz2'.resolve_left h2⟩ hval

/-- Original `PERM_MAP_BIJ`: a bijection preserves and reflects permutation. -/
@[hol "cakeml/misc/miscScript.sml" "PERM_MAP_BIJ"]
theorem permMapBij {α β : Type} (f : α → β) (l1 l2 : List α)
    (hbij : holBij f (fun _ => True) (fun _ => True)) :
    List.Perm l1 l2 ↔ List.Perm (l1.map f) (l2.map f) := by
  classical
  have hinj : ∀ x y, f x = f y → x = y := by
    intro x y h
    exact hbij.1.2 x y ⟨trivial, trivial⟩ h
  have hsurj : ∀ y, ∃ x, f x = y := by
    intro y
    obtain ⟨x, _, hx⟩ := hbij.2.2 y trivial
    exact ⟨x, hx⟩
  have hleft : ∀ x, Classical.choose (hsurj (f x)) = x := by
    intro x
    have h1 : f (Classical.choose (hsurj (f x))) = f x :=
      Classical.choose_spec (hsurj (f x))
    exact hinj _ _ h1
  have hmapAll : ∀ (l : List α),
      (l.map f).map (fun y => Classical.choose (hsurj y)) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨hleft a, ih⟩
  constructor
  · intro h
    exact h.map f
  · intro h
    have hperm := h.map (fun y => Classical.choose (hsurj y))
    rw [hmapAll l1, hmapAll l2] at hperm
    exact hperm

end Flapjack
