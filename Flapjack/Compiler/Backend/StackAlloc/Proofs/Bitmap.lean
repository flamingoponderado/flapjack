import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec

/-!
# `stack_allocProof` bitmap list lemmas

The `filter_bitmap`/`map_bitmap` lemmas of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` used by the
`word_gc_move_bitmap*``word_gc_move_bitmap*` unrolling theorems, over the exact list-level
`Flapjack.StackSem.filterBitmap`/`mapBitmap`, and `enc_dec_stack` over the
exact `encStack`/`decStack`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack.StackSem

/-- Exact HOL `map_bitmap_APPEND` (`stack_allocProofScript.sml:100-117`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "map_bitmap_APPEND"]
theorem map_bitmap_APPEND {α : Type} {q' : List α} :
    ∀ (x : List Bool) (q stack p0 p1 : List α),
      filterBitmap x stack = some (p0, p1) ∧ q.length = p0.length →
      mapBitmap x (q ++ q') stack =
        match mapBitmap x q stack with
        | none => none
        | some (hd, ts, ws) => some (hd, ts ++ q', ws) := by
  intro x
  induction x with
  | nil => intro q stack p0 p1 ⟨h, hl⟩; simp [filterBitmap] at h; simp [mapBitmap]
  | cons b bs ih =>
      intro q stack p0 p1 ⟨h, hl⟩
      cases stack with
      | nil => cases b <;> simp [filterBitmap] at h
      | cons v vs =>
          cases b with
          | false =>
              simp only [filterBitmap] at h
              simp only [mapBitmap, ih q vs p0 p1 ⟨h, hl⟩]
              cases mapBitmap bs q vs with
              | none => rfl
              | some r => rfl
          | true =>
              cases hf : filterBitmap bs vs with
              | none => simp [filterBitmap, hf] at h
              | some pr =>
                  obtain ⟨sel, rest⟩ := pr
                  simp only [filterBitmap, hf, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  cases q with
                  | nil => simp at hl
                  | cons y ys =>
                      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
                      simp only [List.cons_append, mapBitmap, ih ys vs sel rest ⟨hf, hl⟩]
                      cases mapBitmap bs ys vs with
                      | none => rfl
                      | some r => rfl

/-- Exact HOL `filter_bitmap_map_bitmap` (`stack_allocProofScript.sml:119-148`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_map_bitmap"]
theorem filter_bitmap_map_bitmap {α : Type} :
    ∀ (x : List Bool) (t q xs xs1 z ys ys1 : List α),
      filterBitmap x t = some (xs, xs1) ∧ q.length = xs.length ∧
        mapBitmap x q t = some (ys, z, ys1) →
      z = [] ∧ ys1 = xs1 := by
  intro x
  induction x with
  | nil =>
      intro t q xs xs1 z ys ys1 ⟨h1, hl, h2⟩
      simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at h1
      simp only [mapBitmap, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨-, rfl, rfl⟩ := h2
      simp at hl
      exact ⟨hl, rfl⟩
  | cons b bs ih =>
      intro t q xs xs1 z ys ys1 ⟨h1, hl, h2⟩
      cases t with
      | nil => cases b <;> simp [filterBitmap] at h1
      | cons v vs =>
          cases b with
          | false =>
              simp only [filterBitmap] at h1
              simp only [mapBitmap] at h2
              cases hm : mapBitmap bs q vs with
              | none => simp [hm] at h2
              | some r =>
                  obtain ⟨a, b2, c⟩ := r
                  simp only [hm, Option.some.injEq, Prod.mk.injEq] at h2
                  obtain ⟨-, rfl, rfl⟩ := h2
                  exact ih vs q xs xs1 b2 a c ⟨h1, hl, hm⟩
          | true =>
              cases hf : filterBitmap bs vs with
              | none => simp [filterBitmap, hf] at h1
              | some pr =>
                  obtain ⟨sel, rest⟩ := pr
                  simp only [filterBitmap, hf, Option.some.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  cases q with
                  | nil => simp [mapBitmap] at h2
                  | cons y yq =>
                      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
                      simp only [mapBitmap] at h2
                      cases hm : mapBitmap bs yq vs with
                      | none => simp [hm] at h2
                      | some r =>
                          obtain ⟨a, b2, c⟩ := r
                          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h2
                          obtain ⟨-, rfl, rfl⟩ := h2
                          exact ih vs yq sel rest b2 a c ⟨hf, hl, hm⟩

/-- Exact HOL `filter_bitmap_APPEND` (`stack_allocProofScript.sml:209-224`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_APPEND"]
theorem filter_bitmap_APPEND {α : Type} :
    ∀ (xs : List Bool) (stack : List α) (ys : List Bool),
      filterBitmap (xs ++ ys) stack =
        match filterBitmap xs stack with
        | none => none
        | some (zs, rs) =>
            match filterBitmap ys rs with
            | none => none
            | some (zs2, rs) => some (zs ++ zs2, rs) := by
  intro xs
  induction xs with
  | nil =>
      intro stack ys
      simp only [List.nil_append, filterBitmap]
      cases filterBitmap ys stack with
      | none => rfl
      | some r => rfl
  | cons b bs ih =>
      intro stack ys
      cases stack with
      | nil => cases b <;> rfl
      | cons v vs =>
          cases b with
          | false => simp only [List.cons_append, filterBitmap, ih]
          | true =>
              simp only [List.cons_append, filterBitmap, ih]
              rcases filterBitmap bs vs with _ | ⟨zs, rs⟩
              · rfl
              · dsimp only
                rcases filterBitmap ys rs with _ | ⟨zs2, rs2⟩ <;> rfl

/-- Exact HOL `map_bitmap_IMP_LENGTH` (`stack_allocProofScript.sml:327-335`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "map_bitmap_IMP_LENGTH"]
theorem map_bitmap_IMP_LENGTH {α : Type} :
    ∀ (x : List Bool) (wl stack xs : List α) (ys : List α × List α),
      mapBitmap x wl stack = some (xs, ys) → xs.length = x.length := by
  intro x
  induction x with
  | nil =>
      intro wl stack xs ys h
      simp only [mapBitmap, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
  | cons b bs ih =>
      intro wl stack xs ys h
      cases b <;> cases stack <;> (try cases wl) <;> simp only [mapBitmap] at h
      all_goals
        first
        | exact absurd h (by simp)
        | (split at h
           · exact absurd h (by simp)
           · rename_i hm
             simp only [Option.some.injEq, Prod.mk.injEq] at h
             rw [← h.1]; simp [ih _ _ _ _ hm])

/-- Exact HOL `filter_bitmap_IMP_LENGTH` (`stack_allocProofScript.sml:337-345`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_IMP_LENGTH"]
theorem filter_bitmap_IMP_LENGTH {α : Type} :
    ∀ (x : List Bool) (stack q r : List α),
      filterBitmap x stack = some (q, r) → stack.length = x.length + r.length := by
  intro x
  induction x with
  | nil =>
      intro stack q r h
      simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; simp
  | cons b bs ih =>
      intro stack q r h
      cases stack with
      | nil => cases b <;> simp [filterBitmap] at h
      | cons v vs =>
          cases b with
          | false =>
              simp only [filterBitmap] at h
              have := ih vs q r h
              simp; omega
          | true =>
              simp only [filterBitmap] at h
              split at h
              · exact absurd h (by simp)
              · rename_i sel rest hf
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                have := ih vs sel rest hf
                simp; omega

/-- Exact HOL `filter_bitmap_map_bitmap_IMP` (`stack_allocProofScript.sml:4984-4996`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_map_bitmap_IMP"]
theorem filter_bitmap_map_bitmap_IMP {α : Type} :
    ∀ (x : List Bool) (ws q r x' q' q'' r'' : List α),
      filterBitmap x ws = some (q, r) ∧ mapBitmap x (q ++ x') ws = some (q', q'', r'') →
      q'' = x' ∧ r = r'' ∧ ws = q' ++ r := by
  intro x
  induction x with
  | nil =>
      intro ws q r x' q' q'' r'' ⟨h1, h2⟩
      simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simp only [mapBitmap, List.nil_append, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      simp
  | cons b bs ih =>
      intro ws q r x' q' q'' r'' ⟨h1, h2⟩
      cases ws with
      | nil => cases b <;> simp [filterBitmap] at h1
      | cons v vs =>
          cases b with
          | false =>
              simp only [filterBitmap] at h1
              simp only [mapBitmap] at h2
              split at h2
              · exact absurd h2 (by simp)
              · rename_i a b2 c hm
                simp only [Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨rfl, rfl, rfl⟩ := h2
                obtain ⟨e1, e2, e3⟩ := ih vs q r x' a b2 c ⟨h1, hm⟩
                exact ⟨e1, e2, by simp [e3]⟩
          | true =>
              simp only [filterBitmap] at h1
              split at h1
              · exact absurd h1 (by simp)
              · rename_i sel rest hf
                simp only [Option.some.injEq, Prod.mk.injEq] at h1
                obtain ⟨rfl, rfl⟩ := h1
                simp only [List.cons_append, mapBitmap] at h2
                split at h2
                · exact absurd h2 (by simp)
                · rename_i a b2 c hm
                  simp only [Option.some.injEq, Prod.mk.injEq] at h2
                  obtain ⟨rfl, rfl, rfl⟩ := h2
                  obtain ⟨e1, e2, e3⟩ := ih vs sel rest x' a b2 c ⟨hf, hm⟩
                  exact ⟨e1, e2, by simp [e3]⟩

/-- Exact HOL `enc_dec_stack` (`stack_allocProofScript.sml:4998-5016`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "enc_dec_stack"
  (words_as_type_indexed_bitvec)]
theorem enc_dec_stack {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width] :
    ∀ (bs : List (BitVec bitmapWidth)) (ys2 x1 x2 : List (WordLocW width)),
      encStack bs ys2 = some x1 ∧ decStack bs x1 ys2 = some x2 → ys2 = x2 := by
  intro bs ys2
  induction h : ys2.length using Nat.strongRecOn generalizing ys2 with
  | _ n ih =>
    intro x1 x2 ⟨h1, h2⟩
    match ys2 with
    | [] => simp [encStack] at h1
    | header :: tail =>
      rw [encStack] at h1
      rw [decStack] at h2
      by_cases hz : header = .word 0
      · simp only [hz, if_true] at h1 h2
        split at h1
        · rename_i ht
          simp only [Option.some.injEq] at h1
          subst h1 ht
          simp at h2
          rw [← h2, hz]; rfl
        · exact absurd h1 (by simp)
      · simp only [hz, if_false] at h1 h2
        split at h1
        · exact absurd h1 (by simp)
        · rename_i bits hb
          simp only [hb] at h2
          split at h1
          · exact absurd h1 (by simp)
          · rename_i sel rem hf
            split at h1
            · exact absurd h1 (by simp)
            · rename_i roots he
              simp only [Option.some.injEq] at h1
              subst h1
              split at h2
              · exact absurd h2 (by simp)
              · rename_i front rr rem' hm
                obtain ⟨e1, e2, e3⟩ := filter_bitmap_map_bitmap_IMP bits tail sel rem roots front rr rem'
                  ⟨hf, hm⟩
                subst e1 e2
                split at h2
                · exact absurd h2 (by simp)
                · rename_i rest hd
                  simp only [Option.some.injEq] at h2
                  have hlen : rem.length < n := by
                    rw [← h, e3]; simp; omega
                  have := ih rem.length hlen rem rfl _ rest ⟨he, hd⟩
                  rw [← h2, ← this, e3]
                  simp

end Flapjack.Compiler.Backend.StackAlloc
