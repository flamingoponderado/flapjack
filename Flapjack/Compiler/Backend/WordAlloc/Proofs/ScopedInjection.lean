module

public import Flapjack.HolRef

@[expose] public section

namespace Flapjack.WordAlloc

/-- HOL union-scoped injection restricts to each constituent. Predicate sets
render HOL sets, and the codomain UNIV contributes no range constraint. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_UNION"]
theorem injUnionUniv {α β : Type} (f : α → β) (a b : α → Prop)
    (h : ∀ x y, (a x ∨ b x) → (a y ∨ b y) → f x = f y → x = y) :
    (∀ x y, a x → a y → f x = f y → x = y) ∧
      (∀ x y, b x → b y → f x = f y → x = y) := by
  exact ⟨fun x y hx hy he => h x y (Or.inl hx) (Or.inl hy) he,
    fun x y hx hy he => h x y (Or.inr hx) (Or.inr hy) he⟩

/-- HOL injection restriction keeps the original conjunction of scoped
injection and subset inclusion. No global injection premise is introduced. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_less"]
theorem injLess {α β : Type} (f : α → β) (smaller larger : α → Prop)
    (h : (∀ x y, larger x → larger y → f x = f y → x = y) ∧
      (∀ x, smaller x → larger x)) :
    ∀ x y, smaller x → smaller y → f x = f y → x = y := by
  intro x y hx hy he
  exact h.1 x y (h.2 x hx) (h.2 y hy) he

/-- Exact HOL image-of-difference set equality under injection on the union
of the two source sets. Existentials render IMAGE and negation renders DIFF. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_IMP_IMAGE_DIFF"]
theorem injImageDiff {α β : Type} (f : α → β) (s t : α → Prop)
    (h : ∀ x y, (s x ∨ t x) → (s y ∨ t y) → f x = f y → x = y) :
    (fun y => ∃ x, (s x ∧ ¬ t x) ∧ f x = y) =
      (fun y => (∃ x, s x ∧ f x = y) ∧ ¬ (∃ x, t x ∧ f x = y)) := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, ⟨hx, hnt⟩, hxy⟩
    refine ⟨⟨x, hx, hxy⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    have he := h x z (Or.inl hx) (Or.inr hz) (hxy.trans hzy.symm)
    exact hnt (he.symm ▸ hz)
  · rintro ⟨⟨x, hx, hxy⟩, hnt⟩
    exact ⟨x, ⟨hx, fun ht => hnt ⟨x, ht, hxy⟩⟩, hxy⟩

/-- Exact HOL singleton image-difference equality, in the source's reverse
orientation: remove f n from IMAGE f s, or remove n before taking IMAGE. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_IMP_IMAGE_DIFF_single"]
theorem injImageDiffSingle {α β : Type} (f : α → β) (s : α → Prop) (n : α)
    (h : ∀ x y, (s x ∨ x = n) → (s y ∨ y = n) → f x = f y → x = y) :
    (fun y => (∃ x, s x ∧ f x = y) ∧ y ≠ f n) =
      (fun y => ∃ x, (s x ∧ x ≠ n) ∧ f x = y) := by
  funext y
  apply propext
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hne⟩
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    intro he
    subst x
    exact hne hxy.symm
  · rintro ⟨x, ⟨hx, hne⟩, hxy⟩
    refine ⟨⟨x, hx, hxy⟩, ?_⟩
    intro hy
    exact hne (h x n (Or.inl hx) (Or.inr rfl) (hxy.trans hy))

/-- Exact HOL `SUBSET_OF_INSERT` (`word_allocProofScript.sml:27-30`): a set is
included in itself with one extra element inserted. HOL sets are predicates. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "SUBSET_OF_INSERT"]
theorem subsetOfInsert {α : Type} (s : α → Prop) (x : α) :
    ∀ y, s y → y = x ∨ s y := by
  intro y hy
  exact Or.inr hy

/-- Exact HOL `INJ_ALL_DISTINCT_MAP` (`word_allocProofScript.sml:79-84`): a
mapping with distinct image is injective on the list's element set. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_ALL_DISTINCT_MAP"]
theorem injAllDistinctMap {α β : Type} (f : α → β) :
    ∀ ls : List α, (ls.map f).Nodup →
      ∀ x y, x ∈ ls → y ∈ ls → f x = f y → x = y := by
  intro ls
  induction ls with
  | nil =>
      intro _ x y hx _ _
      simp at hx
  | cons a as ih =>
      intro hnd x y hx hy he
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hxa : x = a
      · subst x
        by_cases hya : y = a
        · subst y
          rfl
        · have hyas : y ∈ as := by
            rcases List.mem_cons.mp hy with h | h
            · exact absurd h hya
            · exact h
          exact absurd (he ▸ List.mem_map.mpr ⟨y, hyas, rfl⟩) hnd.1
      · have hxas : x ∈ as := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hxa
          · exact h
        by_cases hya : y = a
        · subst y
          exact absurd (he.symm ▸ List.mem_map.mpr ⟨x, hxas, rfl⟩) hnd.1
        · have hyas : y ∈ as := by
            rcases List.mem_cons.mp hy with h | h
            · exact absurd h hya
            · exact h
          exact ih hnd.2 x y hxas hyas he

end Flapjack.WordAlloc
