import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileListProps
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
import Flapjack.Misc.ListEl

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Generic indexed lookup in a zipped mapped list. Preserves the original
inhabited element types and opaque HOL EL outside its bound. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "alookup_zip_map_some"]
theorem alookupZipMapSome {α β γ : Type} [Nonempty α] [Nonempty β]
    [DecidableEq γ] (ls : List α) (vs : List β) (i : Nat) (f : α → γ)
    (h : (ls.map f).Nodup ∧ i < ls.length ∧ vs.length = ls.length) :
    holAlookup ((ls.map f).zip vs) (f (holEl i ls)) = some (holEl i vs) := by
  induction ls generalizing vs i with
  | nil => simp at h
  | cons x xs ih =>
      cases vs with
      | nil => simp at h
      | cons y ys =>
          have hn : f x ∉ xs.map f ∧ (xs.map f).Nodup := by
            simpa using h.1
          have hl : ys.length = xs.length := by simpa using h.2.2
          cases i with
          | zero => simp [holEl, holHd, holAlookup]
          | succ i =>
              have hi : i < xs.length := by simpa using h.2.1
              have hm : holEl i xs ∈ xs := by
                rw [holEl_eq_getElem i xs hi]
                exact List.getElem_mem hi
              have he : f x ≠ f (holEl i xs) := by
                intro he
                exact hn.1 (he ▸ List.mem_map.mpr ⟨holEl i xs, hm, rfl⟩)
              simpa [holEl, holAlookup, he] using ih ys i ⟨hn.2, hi, hl⟩

/-- Absent source keys remain absent after an injective domain renaming.
Native tree payload and zipped values are independently generic. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "alookup_zip_map_option_lookup_none"]
theorem alookupZipMapOptionLookupNone {α β γ : Type} [DecidableEq γ]
    (ls : List Nat) (vs : List α) (n : Nat) (ns : Spt β) (f : Nat → γ)
    (h : (∀ x y, sptDomain ns x → sptDomain ns y → f x = f y → x = y) ∧ sptDomain ns n ∧
      n ∉ ls ∧ (∀ v, v ∈ ls → sptDomain ns v) ∧ vs.length = ls.length) :
    holAlookup ((ls.map f).zip vs) (f n) = none := by
  induction ls generalizing vs with
  | nil => rfl
  | cons x xs ih =>
      cases vs with
      | nil => simp at h
      | cons y ys =>
          have he : f x ≠ f n := by
            intro he
            have hx := h.1 x n (h.2.2.2.1 x (by simp)) h.2.1 he
            exact h.2.2.1 (by simp [← hx])
          have ht : ∀ v, v ∈ xs → sptDomain ns v := by
            intro v hv
            exact h.2.2.2.1 v (by simp [hv])
          have hl : ys.length = xs.length := by simpa using h.2.2.2.2
          simpa [holAlookup, he] using
            ih ys ⟨h.1, h.2.1, (by intro hn; exact h.2.2.1 (List.mem_cons_of_mem x hn)), ht, hl⟩

end Flapjack.Compiler.Backend.WordAlloc
