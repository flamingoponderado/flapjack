import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

namespace Flapjack.WordAlloc

/-- Flapjack proof convenience wrapper selecting classical propositional
key equality for the existing association-list lookup infrastructure. This
wrapper has no separate HOL original and adds no equality-law premise. -/
noncomputable def keyLookup {α γ : Type} (entries : List (α × γ)) (key : α) :
    Option γ := @holAlookup α γ (Classical.typeDecidableEq α) entries key

/-- Flapjack factoring of key support for a successful zipped-list lookup.
HOL proves this inline using ALOOKUP_MEM and MEM_ZIP. -/
private theorem keyLookupZipMem {α γ : Type} (keys : List α) (values : List γ)
    (key : α) (value : γ) (h : keyLookup (keys.zip values) key = some value) :
    key ∈ keys := by
  classical
  induction keys generalizing values with
  | nil => simp [keyLookup, holAlookup] at h
  | cons head tail ih =>
      cases values with
      | nil => simp [keyLookup, holAlookup] at h
      | cons v values =>
          by_cases heq : head = key
          · simp [← heq]
          · have ht : keyLookup (tail.zip values) key = some value := by
              simpa [keyLookup, holAlookup, heq] using h
            exact List.mem_cons_of_mem head (ih values ht)

/-- Exact HOL ALOOKUP_key_remap_INJ: scoped injection on the queried key
inserted into the input-key set preserves the entire Option lookup result. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_key_remap_INJ"]
theorem alookupKeyRemapINJ {α β γ : Type} (f : α → β) (n : α)
    (keys : List α) (values : List γ)
    (h : (∀ a b, (a = n ∨ a ∈ keys) → (b = n ∨ b ∈ keys) →
      f a = f b → a = b) ∧ keys.length = values.length) :
    keyLookup (keys.zip values) n = keyLookup ((keys.map f).zip values) (f n) := by
  classical
  induction keys generalizing values with
  | nil => simp [keyLookup, holAlookup]
  | cons head tail ih =>
      cases values with
      | nil => simp [keyLookup, holAlookup]
      | cons value values =>
          have htail : (∀ a b, (a = n ∨ a ∈ tail) → (b = n ∨ b ∈ tail) →
              f a = f b → a = b) ∧ tail.length = values.length := by
            refine ⟨?_, by simpa using h.2⟩
            intro a b ha hb heq
            exact h.1 a b (ha.imp_right (List.mem_cons_of_mem head))
              (hb.imp_right (List.mem_cons_of_mem head)) heq
          by_cases heq : head = n
          · simp [keyLookup, holAlookup, heq]
          · have hne : f head ≠ f n := by
              intro hf
              exact heq (h.1 head n (Or.inr (List.mem_cons_self)) (Or.inl rfl) hf)
            simpa [keyLookup, holAlookup, heq, hne] using ih values htail

/-- Exact HOL ALOOKUP_key_remap_2: successful source lookup and injection
only on the input-key set produce the corresponding renamed success. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_key_remap_2"]
theorem alookupKeyRemapTwo {α β γ : Type} (keys : List α) (values : List γ)
    (f : α → β) (n : α) (value : γ)
    (h : (∀ a b, a ∈ keys ∧ b ∈ keys ∧ f a = f b → a = b) ∧
      keys.length = values.length ∧ keyLookup (keys.zip values) n = some value) :
    keyLookup ((keys.map f).zip values) (f n) = some value := by
  have hn := keyLookupZipMem keys values n value h.2.2
  have heq := alookupKeyRemapINJ f n keys values ⟨?_, h.2.1⟩
  · exact heq.symm.trans h.2.2
  · intro a b ha hb hf
    have ha' : a ∈ keys := ha.elim (fun he => he ▸ hn) id
    have hb' : b ∈ keys := hb.elim (fun he => he ▸ hn) id
    exact h.1 a b ⟨ha', hb', hf⟩

end Flapjack.WordAlloc
