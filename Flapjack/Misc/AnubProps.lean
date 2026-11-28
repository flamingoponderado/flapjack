module

public import Flapjack.Misc.Anub
public import Flapjack.Misc.List
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# `anub` lookup and membership facts

Counterparts of `ALOOKUP_anub`, `MEM_anub_ALOOKUP`, `anub_tl_anub` and
`EVERY_anub_suff` from `cakeml/misc/miscScript.sml`. The set-builder notation
and the list lemmas they need live in this dedicated module: importing
`Mathlib.Data.Set.Basic` into `Flapjack.Misc.Anub` itself changes the global
simp set and the `to` token, which breaks `Flapjack.Compiler.Backend.WordUnreach`.
-/

namespace Flapjack

/-- Original `ALOOKUP_anub`: a key already in the accumulator keeps its pruned
lookup, otherwise the original list is consulted. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_anub"]
theorem alookup_anub {α β : Type} [DecidableEq α] (ls : List (α × β)) (acc : List α) (k : α) :
    List.lookup k (anub ls acc) =
      if k ∈ acc then List.lookup k (anub ls acc) else List.lookup k ls := by
  induction ls generalizing acc with
  | nil => simp [anub]
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    by_cases hka : a ∈ acc
    · simp only [anub, if_pos hka]
      rw [ih acc]
      by_cases hk : k ∈ acc
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk]
        have hne : (k == a) = false := by
          have hka' : k ≠ a := by
            intro heq
            exact hk (heq ▸ hka)
          simpa [beq_iff_eq] using hka'
        simp only [List.lookup_cons, hne]
    · simp only [anub, if_neg hka]
      by_cases hk : k ∈ acc
      · rw [if_pos hk]
      · rw [if_neg hk]
        simp only [List.lookup_cons]
        rw [ih (a :: acc)]
        cases hka2 : (k == a) with
        | true => rfl
        | false =>
          have hne : k ≠ a := by simpa [beq_iff_eq] using hka2
          have hmem : ¬ k ∈ a :: acc := by
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem
            · exact hne heq
            · exact hk hmem
          simp only [if_neg hmem]

/-- Original `MEM_anub_ALOOKUP`: a member of the pruned list is found by the
original lookup. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_anub_ALOOKUP"]
theorem mem_anub_alookup {α β : Type} [DecidableEq α] (ls : List (α × β)) (k : α) (v : β) :
    (k, v) ∈ anub ls [] → List.lookup k ls = some v := by
  intro hmem
  have hnd : ((anub ls []).map Prod.fst).Nodup := by
    have h := anubAllDistinctKeys ls [] (by simp)
    simpa using h
  have h1 : List.lookup k (anub ls []) = some v := (memAlookup (anub ls []) k v hnd).mp hmem
  have h2 := alookup_anub ls [] k
  rw [if_neg (by simp)] at h2
  rw [← h2]
  exact h1

/-- Original `anub_tl_anub`: the tail of a pruned list is again a pruned list,
over subsets of the original entries and of the head key's accumulator. -/
@[hol "cakeml/misc/miscScript.sml" "anub_tl_anub"]
theorem anub_tl_anub {α β : Type} [DecidableEq α] (x : List (α × β)) (y : List α)
    (h : α × β) (t : List (α × β)) (heq : anub x y = h :: t) :
    ∃ a b, t = anub a b ∧ {p | p ∈ a} ⊆ {p | p ∈ x} ∧
      {q | q ∈ b} ⊆ {q | q ∈ (h.1 :: y)} := by
  induction x generalizing y with
  | nil => simp [anub] at heq
  | cons p rest ih =>
    obtain ⟨a0, b0⟩ := p
    by_cases ha : a0 ∈ y
    · rw [anub, if_pos ha] at heq
      obtain ⟨a, b, ht, hsub1, hsub2⟩ := ih y heq
      have hsub1' : {q | q ∈ a} ⊆ {q | q ∈ ((a0, b0) :: rest)} := by
        intro q hq
        exact List.mem_cons_of_mem _ (hsub1 hq)
      exact ⟨a, b, ht, hsub1', hsub2⟩
    · rw [anub, if_neg ha] at heq
      simp only [List.cons.injEq] at heq
      obtain ⟨hpair, ht⟩ := heq
      subst hpair
      have hsub1 : {q | q ∈ rest} ⊆ {q | q ∈ ((a0, b0) :: rest)} := by
        intro q hq
        exact List.mem_cons_of_mem _ hq
      have hsub2 : {q | q ∈ a0 :: y} ⊆ {q | q ∈ ((a0, b0).1 :: y)} := by
        intro q hq
        exact hq
      exact ⟨rest, a0 :: y, ht.symm, hsub1, hsub2⟩

/-- Original `EVERY_anub_suff`: a property that holds of every key/value whose
lookup is defined off the accumulator holds of every kept binding. -/
@[hol "cakeml/misc/miscScript.sml" "EVERY_anub_suff"]
theorem every_anub_suff {α β : Type} [DecidableEq α] (P : α × β → Prop) :
    ∀ (ls : List (α × β)) (acc : List α),
      (∀ x, x ∉ acc → match List.lookup x ls with
        | some v => P (x, v)
        | none => True) →
      ∀ p ∈ anub ls acc, P p := by
  intro ls
  induction ls with
  | nil =>
    intro acc _ p hp
    simp [anub] at hp
  | cons q rest ih =>
    intro acc h p hp
    obtain ⟨a0, b0⟩ := q
    by_cases ha : a0 ∈ acc
    · rw [anub, if_pos ha] at hp
      refine ih acc (fun x hx => ?_) p hp
      have hxa : x ≠ a0 := by
        intro heq
        exact hx (heq ▸ ha)
      have hne : (x == a0) = false := by simpa [beq_iff_eq] using hxa
      have hl := h x hx
      simp only [List.lookup_cons, hne] at hl
      exact hl
    · rw [anub, if_neg ha] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have hsome : List.lookup a0 ((a0, b0) :: rest) = some b0 := by
          simp only [List.lookup_cons]
          split
          · rfl
          · rename_i hbeq
            simp at hbeq
        have h' := h a0 ha
        rw [hsome] at h'
        exact h'
      · refine ih (a0 :: acc) (fun x hx => ?_) p hp
        by_cases hxa : x = a0
        · subst hxa
          exact absurd List.mem_cons_self hx
        · have hne : (x == a0) = false := by simpa [beq_iff_eq] using hxa
          have hacc : x ∉ acc := by
            intro hmem
            exact hx (List.mem_cons_of_mem a0 hmem)
          have hl := h x hacc
          simp only [List.lookup_cons, hne] at hl
          exact hl

end Flapjack
