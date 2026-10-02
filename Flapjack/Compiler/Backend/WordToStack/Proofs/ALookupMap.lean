import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyRemap

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.WordAlloc

-- Logical decisions for the original proposition-valued membership conditional;
-- no decision or equality-law hypothesis is added to any theorem.
attribute [local instance] Classical.propDecidable

/-- Full original association lookup under simultaneous key and payload maps.
The injection domain is exactly the query inserted into the list-key set;
keys outside it and repeated source keys are unrestricted. Independent key
and payload types are retained. Existing `keyLookup` selects propositional
HOL equality without adding a decidable-equality or equality-law premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_MAP_any"]
theorem alookupMapAny {α β γ δ : Type} (f : α × γ → β × δ) (k : α → β)
    (h : β → γ → δ) (ls : List (α × γ)) (a : α) (x : β)
    (hinj : ∀ p q, (p = a ∨ p ∈ ls.map Prod.fst) →
      (q = a ∨ q ∈ ls.map Prod.fst) → k p = k q → p = q)
    (hf : ∀ p q, (p, q) ∈ ls → f (p, q) = (k p, h (k p) q))
    (hx : k a = x) :
    keyLookup (ls.map f) x = (keyLookup ls a).map (h x) := by
  classical
  subst x
  revert hinj hf
  induction ls with
  | nil => intros; simp [keyLookup, holAlookup]
  | cons entry ls ih =>
      rcases entry with ⟨p, q⟩
      intro hinj hf
      have hhead := hf p q (List.mem_cons_self ..)
      have ht : ∀ p q, (p, q) ∈ ls → f (p, q) = (k p, h (k p) q) := by
        intro p q hm
        exact hf p q (List.mem_cons_of_mem _ hm)
      have hi : ∀ u v, (u = a ∨ u ∈ ls.map Prod.fst) →
          (v = a ∨ v ∈ ls.map Prod.fst) → k u = k v → u = v := by
        intro u v hu hv he
        apply hinj u v _ _ he
        · exact hu.imp_right (List.mem_cons_of_mem p)
        · exact hv.imp_right (List.mem_cons_of_mem p)
      by_cases he : p = a
      · subst p
        simp [keyLookup, holAlookup, hhead]
      · have hn : k p ≠ k a := by
          intro hk
          exact he (hinj p a (Or.inr (by simp)) (Or.inl rfl) hk)
        simpa [keyLookup, holAlookup, hhead, he, hn] using ih hi ht

/-- Full original lookup under a pair-valued map whose first projection is
injective on the queried element inserted into the source-list set. It returns
exactly the lookup of the mapped second projections keyed by original elements,
including missing elements and duplicates, with no global-injection premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_MAP_INJ_FST"]
theorem alookupMapInjFst {α β γ : Type} (ls : List α) (f : α → β × γ)
    (x : α) (k : β)
    (hinj : ∀ p q, (p = x ∨ p ∈ ls) → (q = x ∨ q ∈ ls) →
      (f p).1 = (f q).1 → p = q)
    (hk : (f x).1 = k) :
    keyLookup (ls.map f) k = keyLookup (ls.map (fun p => (p, (f p).2))) x := by
  classical
  subst k
  revert hinj
  induction ls with
  | nil => intros; rfl
  | cons p ls ih =>
      intro hinj
      have hi : ∀ u v, (u = x ∨ u ∈ ls) → (v = x ∨ v ∈ ls) →
          (f u).1 = (f v).1 → u = v := by
        intro u v hu hv he
        exact hinj u v (hu.imp_right (List.mem_cons_of_mem p))
          (hv.imp_right (List.mem_cons_of_mem p)) he
      change (if (f p).1 = (f x).1 then some (f p).2 else keyLookup (ls.map f) (f x).1) =
        (if p = x then some (f p).2 else keyLookup (ls.map (fun p => (p, (f p).2))) x)
      by_cases he : p = x
      · simp [he]
      · have hn : (f p).1 ≠ (f x).1 := by
          intro hf
          exact he (hinj p x (Or.inr (List.mem_cons_self ..)) (Or.inl rfl) hf)
        simp only [if_neg he, if_neg hn]
        exact ih hi

/-- Full original identity tabulation lookup for arbitrary keys and arbitrary
lists, without a distinctness assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_ID_TABULATE"]
theorem alookupIdTabulate {α : Type} (ls : List α) (x : α) :
    keyLookup (ls.map (fun p => (p, p))) x = if x ∈ ls then some x else none := by
  classical
  induction ls with
  | nil => simp [keyLookup, holAlookup]
  | cons p ls ih =>
      change (if p = x then some p else keyLookup (ls.map (fun p => (p, p))) x) = _
      by_cases he : p = x
      · simp [he]
      · simp [he, Ne.symm he, ih]

end Flapjack.WordToStackProofs
