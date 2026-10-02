import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcBitmaps

/-!
# `stack_allocProof` bitmap-collector unrolling theorems

The `*_bitmap_unroll`, `*_bitmaps_unroll` and `*_roots_bitmaps` theorems of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml`, which restate the
proof-side collectors of `GcBitmaps.lean` one stack slot, frame or root at a
time.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSem Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.WordGcFunctions

theorem getBits_zero {width : Nat} [NeZero width] : getBits (0#width) = [] := by
  simp [getBits, bitLength_eq]

theorem getBits_one {width : Nat} [NeZero width] : getBits (1#width) = [] := by
  have := (bitLength_eq_1 (w := (1#width))).2 rfl
  simp [getBits, this]

theorem getBits_cons {width : Nat} [NeZero width] {w : BitVec width} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    getBits w = w.getLsbD 0 :: getBits (w >>> (1 : Nat)) := by
  have hb : bitLength w = bitLength (w >>> (1 : Nat)) + 1 := by
    have := bitLength_eq w
    rw [if_neg h0] at this
    exact this
  have hpos : bitLength (w >>> (1 : Nat)) ≠ 0 := by
    intro hz
    have := (bitLength_eq_1 (w := w)).1 (by omega)
    exact h1 this
  unfold getBits
  rw [hb, Nat.add_sub_cancel]
  obtain ⟨n, hn⟩ : ∃ n, bitLength (w >>> (1 : Nat)) = n + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hpos).symm⟩
  rw [hn, Nat.add_sub_cancel, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, BitVec.getLsbD_ushiftRight, Nat.add_comm]

theorem readBitmap_cons_msb {width : Nat} [NeZero width] {y : BitVec width}
    {ys : List (BitVec width)} (h : y.msb = true) :
    readBitmap (y :: ys) = (readBitmap ys).map (getBits y ++ ·) := by
  rw [readBitmap, if_pos h, ← getBits_intro h]
  cases readBitmap ys <;> rfl

theorem readBitmap_cons_not_msb {width : Nat} [NeZero width] {y : BitVec width}
    {ys : List (BitVec width)} (h : ¬ y.msb = true) :
    readBitmap (y :: ys) = some (getBits y) := by
  rw [readBitmap, if_neg h]; rfl

/-- HOL's unnamed `map_bitmap_APPEND_APPEND` (`stack_allocProofScript.sml:718-735`, a
`val` without a theory name), Flapjack infrastructure for the `bitmaps_unroll`
theorems. -/
theorem mapBitmap_append_append {α : Type} :
    ∀ (vs1 : List Bool) (stack x0 x1 ws2 : List α) (vs2 : List Bool) (ws1 : List α),
      filterBitmap vs1 stack = some (x0, x1) → x0.length = ws1.length →
      mapBitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
        match mapBitmap vs1 ws1 stack with
        | none => none
        | some (ts1, ts2, ts3) =>
            match mapBitmap vs2 ws2 ts3 with
            | none => none
            | some (us1, us2, us3) => some (ts1 ++ us1, ts2 ++ us2, us3) := by
  intro vs1
  induction vs1 with
  | nil =>
      intro stack x0 x1 ws2 vs2 ws1 hf hl
      simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have : ws1 = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      subst this
      simp only [List.nil_append, mapBitmap]
      rcases mapBitmap vs2 ws2 stack with _ | ⟨a, b, c⟩ <;> rfl
  | cons b bs ih =>
      intro stack x0 x1 ws2 vs2 ws1 hf hl
      cases stack with
      | nil => cases b <;> simp [filterBitmap] at hf
      | cons v vs =>
          cases b with
          | false =>
              simp only [filterBitmap] at hf
              simp only [List.cons_append, mapBitmap, ih vs x0 x1 ws2 vs2 ws1 hf hl]
              rcases mapBitmap bs ws1 vs with _ | ⟨a, b2, c⟩
              · rfl
              · dsimp only
                rcases mapBitmap vs2 ws2 c with _ | ⟨d, e, f⟩ <;> rfl
          | true =>
              simp only [filterBitmap] at hf
              split at hf
              · exact absurd hf (by simp)
              · rename_i sel rest hfs
                simp only [Option.some.injEq, Prod.mk.injEq] at hf
                obtain ⟨rfl, rfl⟩ := hf
                cases ws1 with
                | nil => simp at hl
                | cons y ys =>
                    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
                    simp only [List.cons_append, mapBitmap, ih vs sel rest ws2 vs2 ys hfs hl]
                    rcases mapBitmap bs ys vs with _ | ⟨a, b2, c⟩
                    · rfl
                    · dsimp only
                      rcases mapBitmap vs2 ws2 c with _ | ⟨d, e, f⟩ <;> rfl

theorem drop_succ_of_drop_eq_cons {α : Type} {l ys : List α} {y : α} {k : Nat}
    (h : l.drop k = y :: ys) : l.drop (k + 1) = ys := by
  rw [← List.drop_drop, h]; rfl

/-- Exact HOL `word_gc_move_bitmap_unroll` (`stack_allocProofScript.sml:823-873`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmap_unroll"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveBitmap_unroll {descWidth : Nat} {width : Nat} [NeZero descWidth]
    [NeZero width] {conf : Config} {w : BitVec descWidth} {stack : List (WordLocW width)}
    {i1 pa1 curr : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool} :
    wordGcMoveBitmap conf (w, stack, i1, pa1, curr, m, dm) =
      if w = 0 then some ([], stack, i1, pa1, m, true) else
      if w = 1 then some ([], stack, i1, pa1, m, true) else
        match stack with
        | [] => none
        | x :: xs =>
            if w &&& 1 = 0 then
              match wordGcMoveBitmap conf (w >>> (1 : Nat), xs, i1, pa1, curr, m, dm) with
              | none => none
              | some (new, stack, i1, pa1, m, c) => some (x :: new, stack, i1, pa1, m, c)
            else
              let (x1, i1, pa1, m1, c1) := wordGcMove conf (x, i1, pa1, curr, m, dm)
              match wordGcMoveBitmap conf (w >>> (1 : Nat), xs, i1, pa1, curr, m1, dm) with
              | none => none
              | some (new, stack, i1, pa1, m, c) => some (x1 :: new, stack, i1, pa1, m, c1 && c) := by
  by_cases h0 : w = 0
  · subst h0; simp [wordGcMoveBitmap, getBits_zero, filterBitmap, mapBitmap, wordGcMoveRoots_nil]
  by_cases h1 : w = 1
  · subst h1
    simp [wordGcMoveBitmap, getBits_one, filterBitmap, mapBitmap, wordGcMoveRoots_nil]
  simp only [h0, h1, if_false]
  have hbits := getBits_cons h0 h1
  have hlsb : (w &&& 1 = 0) ↔ w.getLsbD 0 = false := by
    rw [word_and_one_eq_0_iff]; simp
  cases stack with
  | nil =>
      simp only [wordGcMoveBitmap, hbits]
      cases w.getLsbD 0 <;> simp [filterBitmap]
  | cons x xs =>
      by_cases hb : w.getLsbD 0 = false
      · simp only [hlsb.2 hb, if_true]
        simp only [wordGcMoveBitmap, hbits, hb, filterBitmap, mapBitmap]
        rcases filterBitmap (getBits (w >>> (1 : Nat))) xs with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rcases mapBitmap (getBits (w >>> (1 : Nat)))
            (wordGcMoveRoots conf (ts, i1, pa1, curr, m, dm)).1 xs with _ | ⟨a, b, c⟩ <;> rfl
      · have hb' : w.getLsbD 0 = true := by simpa using hb
        have hne : ¬ (w &&& 1 = 0) := fun h => hb (hlsb.1 h)
        simp only [hne, if_false]
        simp only [wordGcMoveBitmap, hbits, hb', filterBitmap]
        rcases filterBitmap (getBits (w >>> (1 : Nat))) xs with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rw [wordGcMoveRoots_cons]
          generalize wordGcMove conf (x, i1, pa1, curr, m, dm) = r
          obtain ⟨x1, i1', pa1', m1', c1'⟩ := r
          dsimp only
          generalize wordGcMoveRoots conf (ts, i1', pa1', curr, m1', dm) = r2
          obtain ⟨wl, i2, pa2, m2, c2⟩ := r2
          simp only [mapBitmap]
          rcases mapBitmap (getBits (w >>> (1 : Nat))) wl xs with _ | ⟨a, b, c⟩ <;> rfl

/-- Exact HOL `word_gen_gc_move_bitmap_unroll` (`stack_allocProofScript.sml:2414-2467`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_move_bitmap_unroll" (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveBitmap_unroll {descWidth : Nat} {width : Nat} [NeZero descWidth]
    [NeZero width] {conf : Config} {w : BitVec descWidth} {stack : List (WordLocW width)}
    {i1 pa1 ib1 pb1 curr : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} :
    wordGenGcMoveBitmap conf (w, stack, i1, pa1, ib1, pb1, curr, m, dm) =
      if w = 0 then some ([], stack, i1, pa1, ib1, pb1, m, true) else
      if w = 1 then some ([], stack, i1, pa1, ib1, pb1, m, true) else
        match stack with
        | [] => none
        | x :: xs =>
            if w &&& 1 = 0 then
              match wordGenGcMoveBitmap conf (w >>> (1 : Nat), xs, i1, pa1, ib1, pb1, curr, m, dm) with
              | none => none
              | some (new, stack, i1, pa1, ib1, pb1, m, c) =>
                  some (x :: new, stack, i1, pa1, ib1, pb1, m, c)
            else
              let (x1, i1, pa1, ib1, pb1, m1, c1) :=
                wordGenGcMove conf (x, i1, pa1, ib1, pb1, curr, m, dm)
              match wordGenGcMoveBitmap conf (w >>> (1 : Nat), xs, i1, pa1, ib1, pb1, curr, m1, dm) with
              | none => none
              | some (new, stack, i1, pa1, ib1, pb1, m, c) =>
                  some (x1 :: new, stack, i1, pa1, ib1, pb1, m, c1 && c) := by
  by_cases h0 : w = 0
  · subst h0
    simp [wordGenGcMoveBitmap, getBits_zero, filterBitmap, mapBitmap, wordGenGcMoveRoots_nil]
  by_cases h1 : w = 1
  · subst h1
    simp [wordGenGcMoveBitmap, getBits_one, filterBitmap, mapBitmap, wordGenGcMoveRoots_nil]
  simp only [h0, h1, if_false]
  have hbits := getBits_cons h0 h1
  have hlsb : (w &&& 1 = 0) ↔ w.getLsbD 0 = false := by
    rw [word_and_one_eq_0_iff]; simp
  cases stack with
  | nil =>
      simp only [wordGenGcMoveBitmap, hbits]
      cases w.getLsbD 0 <;> simp [filterBitmap]
  | cons x xs =>
      by_cases hb : w.getLsbD 0 = false
      · simp only [hlsb.2 hb, if_true]
        simp only [wordGenGcMoveBitmap, hbits, hb, filterBitmap, mapBitmap]
        rcases filterBitmap (getBits (w >>> (1 : Nat))) xs with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rcases mapBitmap (getBits (w >>> (1 : Nat)))
            (wordGenGcMoveRoots conf (ts, i1, pa1, ib1, pb1, curr, m, dm)).1 xs with
            _ | ⟨a, b, c⟩ <;> rfl
      · have hb' : w.getLsbD 0 = true := by simpa using hb
        have hne : ¬ (w &&& 1 = 0) := fun h => hb (hlsb.1 h)
        simp only [hne, if_false]
        simp only [wordGenGcMoveBitmap, hbits, hb', filterBitmap]
        rcases filterBitmap (getBits (w >>> (1 : Nat))) xs with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rw [wordGenGcMoveRoots_cons]
          generalize wordGenGcMove conf (x, i1, pa1, ib1, pb1, curr, m, dm) = r
          obtain ⟨x1, i1', pa1', ib', pb', m1', c1'⟩ := r
          dsimp only
          generalize wordGenGcMoveRoots conf (ts, i1', pa1', ib', pb', curr, m1', dm) = r2
          obtain ⟨wl, i2, pa2, ib2, pb2, m2, c2⟩ := r2
          simp only [mapBitmap]
          rcases mapBitmap (getBits (w >>> (1 : Nat))) wl xs with _ | ⟨a, b, c⟩ <;> rfl

/-- Exact HOL `word_gen_gc_partial_move_bitmap_unroll` (`stack_allocProofScript.sml:2469-2524`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_partial_move_bitmap_unroll" (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveBitmap_unroll {descWidth : Nat} {width : Nat} [NeZero descWidth]
    [NeZero width] {conf : Config} {w : BitVec descWidth} {stack : List (WordLocW width)}
    {i1 pa1 curr : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {gs rs : BitVec width} :
    wordGenGcPartialMoveBitmap conf (w, stack, i1, pa1, curr, m, dm, gs, rs) =
      if w = 0 then some ([], stack, i1, pa1, m, true) else
      if w = 1 then some ([], stack, i1, pa1, m, true) else
        match stack with
        | [] => none
        | x :: xs =>
            if w &&& 1 = 0 then
              match wordGenGcPartialMoveBitmap conf
                  (w >>> (1 : Nat), xs, i1, pa1, curr, m, dm, gs, rs) with
              | none => none
              | some (new, stack, i1, pa1, m, c) => some (x :: new, stack, i1, pa1, m, c)
            else
              let (x1, i1, pa1, m1, c1) := wordGenGcPartialMove conf (x, i1, pa1, curr, m, dm, gs, rs)
              match wordGenGcPartialMoveBitmap conf
                  (w >>> (1 : Nat), xs, i1, pa1, curr, m1, dm, gs, rs) with
              | none => none
              | some (new, stack, i1, pa1, m, c) => some (x1 :: new, stack, i1, pa1, m, c1 && c) := by
  by_cases h0 : w = 0
  · subst h0
    simp [wordGenGcPartialMoveBitmap, getBits_zero, filterBitmap, mapBitmap,
      wordGenGcPartialMoveRoots_nil]
  by_cases h1 : w = 1
  · subst h1
    simp [wordGenGcPartialMoveBitmap, getBits_one, filterBitmap, mapBitmap,
      wordGenGcPartialMoveRoots_nil]
  simp only [h0, h1, if_false]
  have hbits := getBits_cons h0 h1
  have hlsb : (w &&& 1 = 0) ↔ w.getLsbD 0 = false := by
    rw [word_and_one_eq_0_iff]; simp
  cases stack with
  | nil =>
      simp only [wordGenGcPartialMoveBitmap, hbits]
      cases w.getLsbD 0 <;> simp [filterBitmap]
  | cons x xs =>
      by_cases hb : w.getLsbD 0 = false
      · simp only [hlsb.2 hb, if_true]
        simp only [wordGenGcPartialMoveBitmap, hbits, hb, filterBitmap, mapBitmap]
        rcases filterBitmap (getBits (w >>> (1 : Nat))) xs with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rcases mapBitmap (getBits (w >>> (1 : Nat)))
            (wordGenGcPartialMoveRoots conf (ts, i1, pa1, curr, m, dm, gs, rs)).1 xs with
            _ | ⟨a, b, c⟩ <;> rfl
      · have hb' : w.getLsbD 0 = true := by simpa using hb
        have hne : ¬ (w &&& 1 = 0) := fun h => hb (hlsb.1 h)
        simp only [hne, if_false]
        simp only [wordGenGcPartialMoveBitmap, hbits, hb', filterBitmap]
        rcases filterBitmap (getBits (w >>> (1 : Nat))) xs with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rw [wordGenGcPartialMoveRoots_cons]
          generalize wordGenGcPartialMove conf (x, i1, pa1, curr, m, dm, gs, rs) = r
          obtain ⟨x1, i1', pa1', m1', c1'⟩ := r
          dsimp only
          generalize wordGenGcPartialMoveRoots conf (ts, i1', pa1', curr, m1', dm, gs, rs) = r2
          obtain ⟨wl, i2, pa2, m2, c2⟩ := r2
          simp only [mapBitmap]
          rcases mapBitmap (getBits (w >>> (1 : Nat))) wl xs with _ | ⟨a, b, c⟩ <;> rfl

/-- Exact HOL `word_gc_move_bitmaps_unroll` (`stack_allocProofScript.sml:746-821`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmaps_unroll"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveBitmaps_unroll {descWidth : Nat} {width : Nat} {bitmapWidth : Nat}
    [NeZero descWidth] [NeZero width] [NeZero bitmapWidth] {conf : Config}
    {w : BitVec descWidth} {stack : List (WordLocW width)} {bitmaps : List (BitVec bitmapWidth)}
    {i1 pa1 curr : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {x : List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
      (BitVec width → WordLocW width) × Bool} :
    wordGcMoveBitmaps conf (.word w, stack, bitmaps, i1, pa1, curr, m, dm) = some x ∧
        bitmaps.length < 2 ^ descWidth - 1 ∧ goodDimindex descWidth →
      wordGcMoveBitmaps conf (.word w, stack, bitmaps, i1, pa1, curr, m, dm) =
        match bitmaps.drop (w - 1).toNat with
        | [] => none
        | y :: _ys =>
            match wordGcMoveBitmap conf (y, stack, i1, pa1, curr, m, dm) with
            | none => none
            | some (hd, ws, i2, pa2, m2, c2) =>
                if ¬ y.msb = true then some (hd, ws, i2, pa2, m2, c2) else
                  match wordGcMoveBitmaps conf (.word (w + 1), ws, bitmaps, i2, pa2, curr, m2, dm) with
                  | none => none
                  | some (hd3, ws3, i3, pa3, m3, c3) =>
                      some (hd ++ hd3, ws3, i3, pa3, m3, c2 && c3) := by
  rintro ⟨hx, hlen, -⟩
  have hw0 : w ≠ 0 := by
    rintro rfl; simp [wordGcMoveBitmaps, fullReadBitmap] at hx
  rcases hd : bitmaps.drop (w - 1).toNat with _ | ⟨y, ys⟩
  · simp only [wordGcMoveBitmaps, fullReadBitmap, hw0, if_false, hd, readBitmap]
  · dsimp only
    have hk : (w - 1).toNat < bitmaps.length := by
      rcases Nat.lt_or_ge (w - 1).toNat bitmaps.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hd; simp at hd
    have hwsucc : w.toNat = (w - 1).toNat + 1 := by
      have := bitVec_toNat_sub_one_lt hw0
      have h1 : (w - 1 + 1) = w := BitVec.sub_add_cancel w 1
      have := congrArg BitVec.toNat h1
      rw [BitVec.toNat_add] at this
      have hone : (1 : BitVec descWidth).toNat = 1 :=
        by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (Nat.pos_of_ne_zero (NeZero.ne _))]
      rw [hone] at this
      have hlt : (w - 1).toNat + 1 < 2 ^ descWidth := by omega
      rw [Nat.mod_eq_of_lt hlt] at this
      omega
    have hw1 : w + 1 ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      have hone : (1 : BitVec descWidth).toNat = 1 :=
        by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (Nat.pos_of_ne_zero (NeZero.ne _))]
      rw [BitVec.toNat_add, hone, Nat.mod_eq_of_lt (by omega)] at this
      simp at this
    have hdrop : bitmaps.drop (w + 1 - 1).toNat = ys := by
      rw [show w + 1 - 1 = w from BitVec.add_sub_cancel w 1, hwsucc]
      exact drop_succ_of_drop_eq_cons hd
    by_cases hm : y.msb = true
    · simp only [hm, not_true_eq_false, if_false]
      simp only [wordGcMoveBitmaps, fullReadBitmap, hw0, hw1, if_false, hd, hdrop,
        readBitmap_cons_msb hm, wordGcMoveBitmap]
      rcases readBitmap ys with _ | bs2
      · dsimp only
        rcases filterBitmap (getBits y) stack with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rcases mapBitmap (getBits y) (wordGcMoveRoots conf (ts, i1, pa1, curr, m, dm)).1 stack with
            _ | ⟨a, b⟩ <;> rfl
      · simp only [Option.map_some]
        rw [filter_bitmap_APPEND]
        rcases hf1 : filterBitmap (getBits y) stack with _ | ⟨ts1, r1⟩
        · rfl
        · dsimp only
          rcases hf2 : filterBitmap bs2 r1 with _ | ⟨ts2, r2⟩
          · dsimp only
            rcases mapBitmap (getBits y) (wordGcMoveRoots conf (ts1, i1, pa1, curr, m, dm)).1 stack with
              _ | ⟨a, b⟩ <;> simp [hf2]
          · dsimp only
            rw [wordGcMoveRoots_APPEND]
            generalize hR1 : wordGcMoveRoots conf (ts1, i1, pa1, curr, m, dm) = R1
            obtain ⟨wl1, i2, pa2, m2, c2⟩ := R1
            dsimp only
            generalize hR2 : wordGcMoveRoots conf (ts2, i2, pa2, curr, m2, dm) = R2
            obtain ⟨wl2, i3, pa3, m3, c3⟩ := R2
            dsimp only
            have hl1 : ts1.length = wl1.length :=
              (wordGcMoveRoots_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ hR1).symm
            rw [mapBitmap_append_append (getBits y) stack ts1 r1 wl2 bs2 wl1 hf1 hl1]
            rcases hm1 : mapBitmap (getBits y) wl1 stack with _ | ⟨h1, z1, s1⟩
            · rfl
            · dsimp only
              obtain ⟨hz, hs⟩ :=
                filter_bitmap_map_bitmap (getBits y) stack wl1 ts1 r1 z1 h1 s1 ⟨hf1, hl1.symm, hm1⟩
              subst hz hs
              rw [hf2]
              dsimp only
              rw [hR2]
              rcases mapBitmap bs2 wl2 s1 with _ | ⟨u1, u2, u3⟩ <;> simp
    · simp only [hm]
      simp only [wordGcMoveBitmaps, fullReadBitmap, hw0, if_false, hd,
        readBitmap_cons_not_msb hm, wordGcMoveBitmap]
      rcases filterBitmap (getBits y) stack with _ | ⟨ts, ws⟩
      · rfl
      · dsimp only
        rcases mapBitmap (getBits y) (wordGcMoveRoots conf (ts, i1, pa1, curr, m, dm)).1 stack with
          _ | ⟨a, b, c⟩ <;> rfl

/-- Exact HOL `word_gen_gc_move_bitmaps_unroll` (`stack_allocProofScript.sml:2257-2332`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_move_bitmaps_unroll"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveBitmaps_unroll {descWidth : Nat} {width : Nat} {bitmapWidth : Nat}
    [NeZero descWidth] [NeZero width] [NeZero bitmapWidth] {conf : Config}
    {w : BitVec descWidth} {stack : List (WordLocW width)} {bitmaps : List (BitVec bitmapWidth)}
    {i1 pa1 ib1 pb1 curr : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {x : List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
      BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool} :
    wordGenGcMoveBitmaps conf (.word w, stack, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) = some x ∧
        bitmaps.length < 2 ^ descWidth - 1 ∧ goodDimindex descWidth →
      wordGenGcMoveBitmaps conf (.word w, stack, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) =
        match bitmaps.drop (w - 1).toNat with
        | [] => none
        | y :: _ys =>
            match wordGenGcMoveBitmap conf (y, stack, i1, pa1, ib1, pb1, curr, m, dm) with
            | none => none
            | some (hd, ws, i2, pa2, ib2, pb2, m2, c2) =>
                if ¬ y.msb = true then some (hd, ws, i2, pa2, ib2, pb2, m2, c2) else
                  match wordGenGcMoveBitmaps conf (.word (w + 1), ws, bitmaps, i2, pa2, ib2, pb2, curr, m2, dm) with
                  | none => none
                  | some (hd3, ws3, i3, pa3, ib3, pb3, m3, c3) =>
                      some (hd ++ hd3, ws3, i3, pa3, ib3, pb3, m3, c2 && c3) := by
  rintro ⟨hx, hlen, -⟩
  have hw0 : w ≠ 0 := by
    rintro rfl; simp [wordGenGcMoveBitmaps, fullReadBitmap] at hx
  rcases hd : bitmaps.drop (w - 1).toNat with _ | ⟨y, ys⟩
  · simp only [wordGenGcMoveBitmaps, fullReadBitmap, hw0, if_false, hd, readBitmap]
  · dsimp only
    have hk : (w - 1).toNat < bitmaps.length := by
      rcases Nat.lt_or_ge (w - 1).toNat bitmaps.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hd; simp at hd
    have hwsucc : w.toNat = (w - 1).toNat + 1 := by
      have := bitVec_toNat_sub_one_lt hw0
      have h1 : (w - 1 + 1) = w := BitVec.sub_add_cancel w 1
      have := congrArg BitVec.toNat h1
      rw [BitVec.toNat_add] at this
      have hone : (1 : BitVec descWidth).toNat = 1 :=
        by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (Nat.pos_of_ne_zero (NeZero.ne _))]
      rw [hone] at this
      have hlt : (w - 1).toNat + 1 < 2 ^ descWidth := by omega
      rw [Nat.mod_eq_of_lt hlt] at this
      omega
    have hw1 : w + 1 ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      have hone : (1 : BitVec descWidth).toNat = 1 :=
        by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (Nat.pos_of_ne_zero (NeZero.ne _))]
      rw [BitVec.toNat_add, hone, Nat.mod_eq_of_lt (by omega)] at this
      simp at this
    have hdrop : bitmaps.drop (w + 1 - 1).toNat = ys := by
      rw [show w + 1 - 1 = w from BitVec.add_sub_cancel w 1, hwsucc]
      exact drop_succ_of_drop_eq_cons hd
    by_cases hm : y.msb = true
    · simp only [hm, not_true_eq_false, if_false]
      simp only [wordGenGcMoveBitmaps, fullReadBitmap, hw0, hw1, if_false, hd, hdrop,
        readBitmap_cons_msb hm, wordGenGcMoveBitmap]
      rcases readBitmap ys with _ | bs2
      · dsimp only
        rcases filterBitmap (getBits y) stack with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rcases mapBitmap (getBits y) (wordGenGcMoveRoots conf (ts, i1, pa1, ib1, pb1, curr, m, dm)).1 stack with
            _ | ⟨a, b⟩ <;> rfl
      · simp only [Option.map_some]
        rw [filter_bitmap_APPEND]
        rcases hf1 : filterBitmap (getBits y) stack with _ | ⟨ts1, r1⟩
        · rfl
        · dsimp only
          rcases hf2 : filterBitmap bs2 r1 with _ | ⟨ts2, r2⟩
          · dsimp only
            rcases mapBitmap (getBits y) (wordGenGcMoveRoots conf (ts1, i1, pa1, ib1, pb1, curr, m, dm)).1 stack with
              _ | ⟨a, b⟩ <;> simp [hf2]
          · dsimp only
            rw [wordGenGcMoveRoots_APPEND]
            generalize hR1 : wordGenGcMoveRoots conf (ts1, i1, pa1, ib1, pb1, curr, m, dm) = R1
            obtain ⟨wl1, i2, pa2, ib2, pb2, m2, c2⟩ := R1
            dsimp only
            generalize hR2 : wordGenGcMoveRoots conf (ts2, i2, pa2, ib2, pb2, curr, m2, dm) = R2
            obtain ⟨wl2, i3, pa3, ib3, pb3, m3, c3⟩ := R2
            dsimp only
            have hl1 : ts1.length = wl1.length :=
              (wordGenGcMoveRoots_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR1).symm
            rw [mapBitmap_append_append (getBits y) stack ts1 r1 wl2 bs2 wl1 hf1 hl1]
            rcases hm1 : mapBitmap (getBits y) wl1 stack with _ | ⟨h1, z1, s1⟩
            · rfl
            · dsimp only
              obtain ⟨hz, hs⟩ :=
                filter_bitmap_map_bitmap (getBits y) stack wl1 ts1 r1 z1 h1 s1 ⟨hf1, hl1.symm, hm1⟩
              subst hz hs
              rw [hf2]
              dsimp only
              rw [hR2]
              rcases mapBitmap bs2 wl2 s1 with _ | ⟨u1, u2, u3⟩ <;> simp
    · simp only [hm]
      simp only [wordGenGcMoveBitmaps, fullReadBitmap, hw0, if_false, hd,
        readBitmap_cons_not_msb hm, wordGenGcMoveBitmap]
      rcases filterBitmap (getBits y) stack with _ | ⟨ts, ws⟩
      · rfl
      · dsimp only
        rcases mapBitmap (getBits y) (wordGenGcMoveRoots conf (ts, i1, pa1, ib1, pb1, curr, m, dm)).1 stack with
          _ | ⟨a, b, c⟩ <;> rfl

/-- Exact HOL `word_gen_gc_partial_move_bitmaps_unroll` (`stack_allocProofScript.sml:2334-2412`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_partial_move_bitmaps_unroll" (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveBitmaps_unroll {descWidth : Nat} {width : Nat} {bitmapWidth : Nat}
    [NeZero descWidth] [NeZero width] [NeZero bitmapWidth] {conf : Config}
    {w : BitVec descWidth} {stack : List (WordLocW width)} {bitmaps : List (BitVec bitmapWidth)}
    {i1 pa1 curr : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool} {gs rs : BitVec width}
    {x : List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
      (BitVec width → WordLocW width) × Bool} :
    wordGenGcPartialMoveBitmaps conf (.word w, stack, bitmaps, i1, pa1, curr, m, dm, gs, rs) = some x ∧
        bitmaps.length < 2 ^ descWidth - 1 ∧ goodDimindex descWidth →
      wordGenGcPartialMoveBitmaps conf (.word w, stack, bitmaps, i1, pa1, curr, m, dm, gs, rs) =
        match bitmaps.drop (w - 1).toNat with
        | [] => none
        | y :: _ys =>
            match wordGenGcPartialMoveBitmap conf (y, stack, i1, pa1, curr, m, dm, gs, rs) with
            | none => none
            | some (hd, ws, i2, pa2, m2, c2) =>
                if ¬ y.msb = true then some (hd, ws, i2, pa2, m2, c2) else
                  match wordGenGcPartialMoveBitmaps conf (.word (w + 1), ws, bitmaps, i2, pa2, curr, m2, dm, gs, rs) with
                  | none => none
                  | some (hd3, ws3, i3, pa3, m3, c3) =>
                      some (hd ++ hd3, ws3, i3, pa3, m3, c2 && c3) := by
  rintro ⟨hx, hlen, -⟩
  have hw0 : w ≠ 0 := by
    rintro rfl; simp [wordGenGcPartialMoveBitmaps, fullReadBitmap] at hx
  rcases hd : bitmaps.drop (w - 1).toNat with _ | ⟨y, ys⟩
  · simp only [wordGenGcPartialMoveBitmaps, fullReadBitmap, hw0, if_false, hd, readBitmap]
  · dsimp only
    have hk : (w - 1).toNat < bitmaps.length := by
      rcases Nat.lt_or_ge (w - 1).toNat bitmaps.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hd; simp at hd
    have hwsucc : w.toNat = (w - 1).toNat + 1 := by
      have := bitVec_toNat_sub_one_lt hw0
      have h1 : (w - 1 + 1) = w := BitVec.sub_add_cancel w 1
      have := congrArg BitVec.toNat h1
      rw [BitVec.toNat_add] at this
      have hone : (1 : BitVec descWidth).toNat = 1 :=
        by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (Nat.pos_of_ne_zero (NeZero.ne _))]
      rw [hone] at this
      have hlt : (w - 1).toNat + 1 < 2 ^ descWidth := by omega
      rw [Nat.mod_eq_of_lt hlt] at this
      omega
    have hw1 : w + 1 ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      have hone : (1 : BitVec descWidth).toNat = 1 :=
        by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (Nat.pos_of_ne_zero (NeZero.ne _))]
      rw [BitVec.toNat_add, hone, Nat.mod_eq_of_lt (by omega)] at this
      simp at this
    have hdrop : bitmaps.drop (w + 1 - 1).toNat = ys := by
      rw [show w + 1 - 1 = w from BitVec.add_sub_cancel w 1, hwsucc]
      exact drop_succ_of_drop_eq_cons hd
    by_cases hm : y.msb = true
    · simp only [hm, not_true_eq_false, if_false]
      simp only [wordGenGcPartialMoveBitmaps, fullReadBitmap, hw0, hw1, if_false, hd, hdrop,
        readBitmap_cons_msb hm, wordGenGcPartialMoveBitmap]
      rcases readBitmap ys with _ | bs2
      · dsimp only
        rcases filterBitmap (getBits y) stack with _ | ⟨ts, ws⟩
        · rfl
        · dsimp only
          rcases mapBitmap (getBits y) (wordGenGcPartialMoveRoots conf (ts, i1, pa1, curr, m, dm, gs, rs)).1 stack with
            _ | ⟨a, b⟩ <;> rfl
      · simp only [Option.map_some]
        rw [filter_bitmap_APPEND]
        rcases hf1 : filterBitmap (getBits y) stack with _ | ⟨ts1, r1⟩
        · rfl
        · dsimp only
          rcases hf2 : filterBitmap bs2 r1 with _ | ⟨ts2, r2⟩
          · dsimp only
            rcases mapBitmap (getBits y) (wordGenGcPartialMoveRoots conf (ts1, i1, pa1, curr, m, dm, gs, rs)).1 stack with
              _ | ⟨a, b⟩ <;> simp [hf2]
          · dsimp only
            rw [wordGenGcPartialMoveRoots_APPEND ts1 ts2 i1 pa1 0 0 m]
            generalize hR1 : wordGenGcPartialMoveRoots conf (ts1, i1, pa1, curr, m, dm, gs, rs) = R1
            obtain ⟨wl1, i2, pa2, m2, c2⟩ := R1
            dsimp only
            generalize hR2 : wordGenGcPartialMoveRoots conf (ts2, i2, pa2, curr, m2, dm, gs, rs) = R2
            obtain ⟨wl2, i3, pa3, m3, c3⟩ := R2
            dsimp only
            have hl1 : ts1.length = wl1.length :=
              (wordGenGcPartialMoveRoots_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR1).symm
            rw [mapBitmap_append_append (getBits y) stack ts1 r1 wl2 bs2 wl1 hf1 hl1]
            rcases hm1 : mapBitmap (getBits y) wl1 stack with _ | ⟨h1, z1, s1⟩
            · rfl
            · dsimp only
              obtain ⟨hz, hs⟩ :=
                filter_bitmap_map_bitmap (getBits y) stack wl1 ts1 r1 z1 h1 s1 ⟨hf1, hl1.symm, hm1⟩
              subst hz hs
              rw [hf2]
              dsimp only
              rw [hR2]
              rcases mapBitmap bs2 wl2 s1 with _ | ⟨u1, u2, u3⟩ <;> simp
    · simp only [hm]
      simp only [wordGenGcPartialMoveBitmaps, fullReadBitmap, hw0, if_false, hd,
        readBitmap_cons_not_msb hm, wordGenGcPartialMoveBitmap]
      rcases filterBitmap (getBits y) stack with _ | ⟨ts, ws⟩
      · rfl
      · dsimp only
        rcases mapBitmap (getBits y) (wordGenGcPartialMoveRoots conf (ts, i1, pa1, curr, m, dm, gs, rs)).1 stack with
          _ | ⟨a, b, c⟩ <;> rfl

theorem encStack_cons_ne {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    {bitmaps : List (BitVec bitmapWidth)} {w : WordLocW width} {ws : List (WordLocW width)}
    (hw : ¬ w = .word 0) :
    encStack bitmaps (w :: ws) =
      match fullReadBitmap bitmaps w with
      | none => none
      | some bits =>
          match filterBitmap bits ws with
          | none => none
          | some (sel, rem) => (encStack bitmaps rem).map (sel ++ ·) := by
  rw [encStack, if_neg hw]
  rcases fullReadBitmap bitmaps w with _ | bits
  · rfl
  · dsimp only
    split
    · rename_i h; rw [h]
    · rename_i sel rem h
      rw [h]; dsimp only
      rcases encStack bitmaps rem <;> rfl

theorem decStack_cons_ne {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    {bitmaps : List (BitVec bitmapWidth)} {roots : List (WordLocW width)} {w : WordLocW width}
    {ws : List (WordLocW width)} (hw : ¬ w = .word 0) :
    decStack bitmaps roots (w :: ws) =
      match fullReadBitmap bitmaps w with
      | none => none
      | some bits =>
          match mapBitmap bits roots ws with
          | none => none
          | some (front, rr, rem) => (decStack bitmaps rr rem).map ([w] ++ front ++ ·) := by
  rw [decStack, if_neg hw]
  rcases fullReadBitmap bitmaps w with _ | bits
  · rfl
  · dsimp only
    split
    · rename_i h; rw [h]
    · rename_i front rr rem h
      rw [h]; dsimp only
      rcases decStack bitmaps rr rem <;> rfl

/-- Exact HOL `word_gc_move_roots_bitmaps` (`stack_allocProofScript.sml:656-704`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_roots_bitmaps"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveRootsBitmaps_unroll {width : Nat} {bitmapWidth : Nat} [NeZero width]
    [NeZero bitmapWidth] {conf : Config} {bitmaps : List (BitVec bitmapWidth)}
    {curr : BitVec width} {dm : BitVec width → Bool} :
    ∀ (stack : List (WordLocW width)) (i1 pa1 : BitVec width) (m : BitVec width → WordLocW width)
      (stack2 : List (WordLocW width)) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width),
      wordGcMoveRootsBitmaps conf (stack, bitmaps, i1, pa1, curr, m, dm) =
          (stack2, i2, pa2, m2, true) →
        wordGcMoveRootsBitmaps conf (stack, bitmaps, i1, pa1, curr, m, dm) =
          match stack with
          | [] => (holArb _, holArb _, holArb _, holArb _, false)
          | w :: ws =>
              if w = .word 0 then (stack, i1, pa1, m, decide (ws = [])) else
                match wordGcMoveBitmaps conf (w, ws, bitmaps, i1, pa1, curr, m, dm) with
                | none => (holArb _, holArb _, holArb _, holArb _, false)
                | some (new, stack, i2, pa2, m2, c2) =>
                    let (stack, i, pa, m, c3) :=
                      wordGcMoveRootsBitmaps conf (stack, bitmaps, i2, pa2, curr, m2, dm)
                    (w :: new ++ stack, i, pa, m, c2 && c3) := by
  intro stack i1 pa1 m stack2 i2 pa2 m2 hx
  rcases stack with _ | ⟨w, ws⟩
  · simp [wordGcMoveRootsBitmaps, encStack]
  dsimp only
  by_cases hw : w = .word 0
  · subst hw
    simp only [if_true]
    by_cases hws : ws = []
    · subst hws
      simp [wordGcMoveRootsBitmaps, encStack, decStack, wordGcMoveRoots_nil]
    · exfalso
      simp [wordGcMoveRootsBitmaps, encStack, hws] at hx
  simp only [hw, if_false]
  rcases hb : fullReadBitmap bitmaps w with _ | bits
  · have he : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]
    simp [wordGcMoveRootsBitmaps, he, wordGcMoveBitmaps, hb]
  rcases hf : filterBitmap bits ws with _ | ⟨sel, rem⟩
  · have he : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]; simp [hf]
    simp [wordGcMoveRootsBitmaps, he, wordGcMoveBitmaps, hb, hf]
  rcases he : encStack bitmaps rem with _ | roots
  · exfalso
    have he' : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]; simp [hf, he]
    simp [wordGcMoveRootsBitmaps, he'] at hx
  have henc : encStack bitmaps (w :: ws) = some (sel ++ roots) := by
    rw [encStack_cons_ne hw, hb]; simp [hf, he]
  generalize hR1 : wordGcMoveRoots conf (sel, i1, pa1, curr, m, dm) = R1
  obtain ⟨wl1, i', pa', m', c1⟩ := R1
  have hl1 : sel.length = wl1.length :=
    (wordGcMoveRoots_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ hR1).symm
  generalize hR2 : wordGcMoveRoots conf (roots, i', pa', curr, m', dm) = R2
  obtain ⟨wl2, i'', pa'', m'', c2⟩ := R2
  have hroots : wordGcMoveRoots conf (sel ++ roots, i1, pa1, curr, m, dm) =
      (wl1 ++ wl2, i'', pa'', m'', c1 && c2) := by
    rw [wordGcMoveRoots_APPEND, hR1]; dsimp only; rw [hR2]
  have happ := map_bitmap_APPEND (q' := wl2) bits wl1 ws sel rem ⟨hf, hl1.symm⟩
  rcases hm : mapBitmap bits wl1 ws with _ | ⟨hd, ts, rest⟩
  · have hbm : wordGcMoveBitmaps conf (w, ws, bitmaps, i1, pa1, curr, m, dm) = none := by
      simp [wordGcMoveBitmaps, hb, hf, hR1, hm]
    have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = none := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm]
    simp [wordGcMoveRootsBitmaps, henc, hroots, hdec, hbm]
  obtain ⟨hts, hrest⟩ := filter_bitmap_map_bitmap bits ws wl1 sel rem ts hd rest ⟨hf, hl1.symm, hm⟩
  subst hts hrest
  have hbm : wordGcMoveBitmaps conf (w, ws, bitmaps, i1, pa1, curr, m, dm) =
      some (hd, rest, i', pa', m', c1) := by
    simp [wordGcMoveBitmaps, hb, hf, hR1, hm]
  rw [hbm]
  dsimp only
  rcases hd2 : decStack bitmaps wl2 rest with _ | st
  · exfalso
    have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = none := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm, hd2]
    simp [wordGcMoveRootsBitmaps, henc, hroots, hdec] at hx
  · have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = some ([w] ++ hd ++ st) := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm, hd2]
    simp [wordGcMoveRootsBitmaps, henc, hroots, hdec, he, hR2, hd2]

/-- Exact HOL `word_gen_gc_move_roots_bitmaps` (`stack_allocProofScript.sml:2091-2142`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_move_roots_bitmaps"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRootsBitmaps_unroll {width : Nat} {bitmapWidth : Nat} [NeZero width]
    [NeZero bitmapWidth] {conf : Config} {bitmaps : List (BitVec bitmapWidth)}
    {curr : BitVec width} {dm : BitVec width → Bool} {ib1 pb1 ib2 pb2 : BitVec width} :
    ∀ (stack : List (WordLocW width)) (i1 pa1 : BitVec width) (m : BitVec width → WordLocW width)
      (stack2 : List (WordLocW width)) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width),
      wordGenGcMoveRootsBitmaps conf (stack, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) =
          (stack2, i2, pa2, ib2, pb2, m2, true) →
        wordGenGcMoveRootsBitmaps conf (stack, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) =
          match stack with
          | [] => (holArb _, holArb _, holArb _, holArb _, holArb _, holArb _, false)
          | w :: ws =>
              if w = .word 0 then (stack, i1, pa1, ib1, pb1, m, decide (ws = [])) else
                match wordGenGcMoveBitmaps conf (w, ws, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) with
                | none => (holArb _, holArb _, holArb _, holArb _, holArb _, holArb _, false)
                | some (new, stack, i2, pa2, ib2, pb2, m2, c2) =>
                    let (stack, i, pa, ib1, pb1, m, c3) :=
                      wordGenGcMoveRootsBitmaps conf (stack, bitmaps, i2, pa2, ib2, pb2, curr, m2, dm)
                    (w :: new ++ stack, i, pa, ib1, pb1, m, c2 && c3) := by
  intro stack i1 pa1 m stack2 i2 pa2 m2 hx
  rcases stack with _ | ⟨w, ws⟩
  · simp [wordGenGcMoveRootsBitmaps, encStack]
  dsimp only
  by_cases hw : w = .word 0
  · subst hw
    simp only [if_true]
    by_cases hws : ws = []
    · subst hws
      simp [wordGenGcMoveRootsBitmaps, encStack, decStack, wordGenGcMoveRoots_nil]
    · exfalso
      simp [wordGenGcMoveRootsBitmaps, encStack, hws] at hx
  simp only [hw, if_false]
  rcases hb : fullReadBitmap bitmaps w with _ | bits
  · have he : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]
    simp [wordGenGcMoveRootsBitmaps, he, wordGenGcMoveBitmaps, hb]
  rcases hf : filterBitmap bits ws with _ | ⟨sel, rem⟩
  · have he : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]; simp [hf]
    simp [wordGenGcMoveRootsBitmaps, he, wordGenGcMoveBitmaps, hb, hf]
  rcases he : encStack bitmaps rem with _ | roots
  · exfalso
    have he' : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]; simp [hf, he]
    simp [wordGenGcMoveRootsBitmaps, he'] at hx
  have henc : encStack bitmaps (w :: ws) = some (sel ++ roots) := by
    rw [encStack_cons_ne hw, hb]; simp [hf, he]
  generalize hR1 : wordGenGcMoveRoots conf (sel, i1, pa1, ib1, pb1, curr, m, dm) = R1
  obtain ⟨wl1, i', pa', ib', pb', m', c1⟩ := R1
  have hl1 : sel.length = wl1.length :=
    (wordGenGcMoveRoots_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR1).symm
  generalize hR2 : wordGenGcMoveRoots conf (roots, i', pa', ib', pb', curr, m', dm) = R2
  obtain ⟨wl2, i'', pa'', ib'', pb'', m'', c2⟩ := R2
  have hroots : wordGenGcMoveRoots conf (sel ++ roots, i1, pa1, ib1, pb1, curr, m, dm) =
      (wl1 ++ wl2, i'', pa'', ib'', pb'', m'', c1 && c2) := by
    rw [wordGenGcMoveRoots_APPEND, hR1]; dsimp only; rw [hR2]
  have happ := map_bitmap_APPEND (q' := wl2) bits wl1 ws sel rem ⟨hf, hl1.symm⟩
  rcases hm : mapBitmap bits wl1 ws with _ | ⟨hd, ts, rest⟩
  · have hbm : wordGenGcMoveBitmaps conf (w, ws, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) = none := by
      simp [wordGenGcMoveBitmaps, hb, hf, hR1, hm]
    have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = none := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm]
    simp [wordGenGcMoveRootsBitmaps, henc, hroots, hdec, hbm]
  obtain ⟨hts, hrest⟩ := filter_bitmap_map_bitmap bits ws wl1 sel rem ts hd rest ⟨hf, hl1.symm, hm⟩
  subst hts hrest
  have hbm : wordGenGcMoveBitmaps conf (w, ws, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) =
      some (hd, rest, i', pa', ib', pb', m', c1) := by
    simp [wordGenGcMoveBitmaps, hb, hf, hR1, hm]
  rw [hbm]
  dsimp only
  rcases hd2 : decStack bitmaps wl2 rest with _ | st
  · exfalso
    have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = none := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm, hd2]
    simp [wordGenGcMoveRootsBitmaps, henc, hroots, hdec] at hx
  · have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = some ([w] ++ hd ++ st) := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm, hd2]
    simp [wordGenGcMoveRootsBitmaps, henc, hroots, hdec, he, hR2, hd2]

/-- Exact HOL `word_gen_gc_partial_move_roots_bitmaps` (`stack_allocProofScript.sml:2144-2197`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_partial_move_roots_bitmaps"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRootsBitmaps_unroll {width : Nat} {bitmapWidth : Nat} [NeZero width]
    [NeZero bitmapWidth] {conf : Config} {bitmaps : List (BitVec bitmapWidth)}
    {curr : BitVec width} {dm : BitVec width → Bool} {gs rs : BitVec width} :
    ∀ (stack : List (WordLocW width)) (i1 pa1 : BitVec width) (m : BitVec width → WordLocW width)
      (stack2 : List (WordLocW width)) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width),
      wordGenGcPartialMoveRootsBitmaps conf (stack, bitmaps, i1, pa1, curr, m, dm, gs, rs) =
          (stack2, i2, pa2, m2, true) →
        wordGenGcPartialMoveRootsBitmaps conf (stack, bitmaps, i1, pa1, curr, m, dm, gs, rs) =
          match stack with
          | [] => (holArb _, holArb _, holArb _, holArb _, false)
          | w :: ws =>
              if w = .word 0 then (stack, i1, pa1, m, decide (ws = [])) else
                match wordGenGcPartialMoveBitmaps conf (w, ws, bitmaps, i1, pa1, curr, m, dm, gs, rs) with
                | none => (holArb _, holArb _, holArb _, holArb _, false)
                | some (new, stack, i2, pa2, m2, c2) =>
                    let (stack, i, pa, m, c3) :=
                      wordGenGcPartialMoveRootsBitmaps conf (stack, bitmaps, i2, pa2, curr, m2, dm, gs, rs)
                    (w :: new ++ stack, i, pa, m, c2 && c3) := by
  intro stack i1 pa1 m stack2 i2 pa2 m2 hx
  rcases stack with _ | ⟨w, ws⟩
  · simp [wordGenGcPartialMoveRootsBitmaps, encStack]
  dsimp only
  by_cases hw : w = .word 0
  · subst hw
    simp only [if_true]
    by_cases hws : ws = []
    · subst hws
      simp [wordGenGcPartialMoveRootsBitmaps, encStack, decStack, wordGenGcPartialMoveRoots_nil]
    · exfalso
      simp [wordGenGcPartialMoveRootsBitmaps, encStack, hws] at hx
  simp only [hw, if_false]
  rcases hb : fullReadBitmap bitmaps w with _ | bits
  · have he : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]
    simp [wordGenGcPartialMoveRootsBitmaps, he, wordGenGcPartialMoveBitmaps, hb]
  rcases hf : filterBitmap bits ws with _ | ⟨sel, rem⟩
  · have he : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]; simp [hf]
    simp [wordGenGcPartialMoveRootsBitmaps, he, wordGenGcPartialMoveBitmaps, hb, hf]
  rcases he : encStack bitmaps rem with _ | roots
  · exfalso
    have he' : encStack bitmaps (w :: ws) = none := by rw [encStack_cons_ne hw, hb]; simp [hf, he]
    simp [wordGenGcPartialMoveRootsBitmaps, he'] at hx
  have henc : encStack bitmaps (w :: ws) = some (sel ++ roots) := by
    rw [encStack_cons_ne hw, hb]; simp [hf, he]
  generalize hR1 : wordGenGcPartialMoveRoots conf (sel, i1, pa1, curr, m, dm, gs, rs) = R1
  obtain ⟨wl1, i', pa', m', c1⟩ := R1
  have hl1 : sel.length = wl1.length :=
    (wordGenGcPartialMoveRoots_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR1).symm
  generalize hR2 : wordGenGcPartialMoveRoots conf (roots, i', pa', curr, m', dm, gs, rs) = R2
  obtain ⟨wl2, i'', pa'', m'', c2⟩ := R2
  have hroots : wordGenGcPartialMoveRoots conf (sel ++ roots, i1, pa1, curr, m, dm, gs, rs) =
      (wl1 ++ wl2, i'', pa'', m'', c1 && c2) := by
    rw [wordGenGcPartialMoveRoots_APPEND sel roots i1 pa1 0 0 m, hR1]; dsimp only; rw [hR2]
  have happ := map_bitmap_APPEND (q' := wl2) bits wl1 ws sel rem ⟨hf, hl1.symm⟩
  rcases hm : mapBitmap bits wl1 ws with _ | ⟨hd, ts, rest⟩
  · have hbm : wordGenGcPartialMoveBitmaps conf (w, ws, bitmaps, i1, pa1, curr, m, dm, gs, rs) = none := by
      simp [wordGenGcPartialMoveBitmaps, hb, hf, hR1, hm]
    have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = none := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm]
    simp [wordGenGcPartialMoveRootsBitmaps, henc, hroots, hdec, hbm]
  obtain ⟨hts, hrest⟩ := filter_bitmap_map_bitmap bits ws wl1 sel rem ts hd rest ⟨hf, hl1.symm, hm⟩
  subst hts hrest
  have hbm : wordGenGcPartialMoveBitmaps conf (w, ws, bitmaps, i1, pa1, curr, m, dm, gs, rs) =
      some (hd, rest, i', pa', m', c1) := by
    simp [wordGenGcPartialMoveBitmaps, hb, hf, hR1, hm]
  rw [hbm]
  dsimp only
  rcases hd2 : decStack bitmaps wl2 rest with _ | st
  · exfalso
    have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = none := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm, hd2]
    simp [wordGenGcPartialMoveRootsBitmaps, henc, hroots, hdec] at hx
  · have hdec : decStack bitmaps (wl1 ++ wl2) (w :: ws) = some ([w] ++ hd ++ st) := by
      rw [decStack_cons_ne hw, hb]; simp [happ, hm, hd2]
    simp [wordGenGcPartialMoveRootsBitmaps, henc, hroots, hdec, he, hR2, hd2]

end Flapjack.Compiler.Backend.StackAlloc
