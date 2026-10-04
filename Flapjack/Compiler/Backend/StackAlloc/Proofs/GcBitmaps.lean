import Flapjack.HolRef
import Flapjack.HolArb
import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Compiler.Backend.WordGcFunctions.Roots
import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Bitmap

/-!
# `stack_allocProof` proof-side GC definitions

The stack-walking collector definitions of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml`
(`word_gc_move_roots_bitmaps`, `word_gc_move_bitmaps`, `word_gc_move_bitmap` and
their generational and partial counterparts) with their `LENGTH`/`APPEND`
lemmas and the loop success lemmas.  HOL infers independent word dimensions for
the frame descriptor, the stack words and the bitmap words; each Lean
declaration binds the same independent widths.  HOL's `ARB` results are
`holArb`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSem Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.WordGcFunctions

/-- Exact HOL `word_gc_move_roots_bitmaps_def` (`stack_allocProofScript.sml:526-536`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGcMoveRootsBitmaps {width : Nat} {bitmapWidth : Nat} [NeZero width]
    [NeZero bitmapWidth] (conf : Config) :
    List (WordLocW width) × List (BitVec bitmapWidth) × BitVec width × BitVec width ×
        BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) ×
        Bool
  | (stack, bitmaps, i1, pa1, curr, m, dm) =>
      match encStack bitmaps stack with
      | none => (holArb _, holArb _, holArb _, holArb _, false)
      | some wlList =>
          let (wl, i2, pa2, m2, c2) := wordGcMoveRoots conf (wlList, i1, pa1, curr, m, dm)
          match decStack bitmaps wl stack with
          | none => (holArb _, holArb _, holArb _, holArb _, false)
          | some stack => (stack, i2, pa2, m2, c2)

/-- Exact HOL `word_gc_move_bitmaps_def` (`stack_allocProofScript.sml:613-627`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGcMoveBitmaps {descWidth : Nat} {width : Nat} {bitmapWidth : Nat} [NeZero descWidth]
    [NeZero width] [NeZero bitmapWidth] (conf : Config) :
    WordLocW descWidth × List (WordLocW width) × List (BitVec bitmapWidth) × BitVec width ×
        BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      Option (List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool)
  | (w, stack, bitmaps, i1, pa1, curr, m, dm) =>
      match fullReadBitmap bitmaps w with
      | none => none
      | some bs =>
          match filterBitmap bs stack with
          | none => none
          | some (ts, ws) =>
              let (wl, i2, pa2, m2, c2) := wordGcMoveRoots conf (ts, i1, pa1, curr, m, dm)
              match mapBitmap bs wl stack with
              | none => none
              | some (hd, _, _) => some (hd, ws, i2, pa2, m2, c2)

/-- Exact HOL `word_gc_move_bitmap_def` (`stack_allocProofScript.sml:706-716`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGcMoveBitmap {descWidth : Nat} {width : Nat} [NeZero descWidth] [NeZero width]
    (conf : Config) :
    BitVec descWidth × List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      Option (List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool)
  | (w, stack, i1, pa1, curr, m, dm) =>
      let bs := getBits w
      match filterBitmap bs stack with
      | none => none
      | some (ts, ws) =>
          let (wl, i2, pa2, m2, c2) := wordGcMoveRoots conf (ts, i1, pa1, curr, m, dm)
          match mapBitmap bs wl stack with
          | none => none
          | some (hd, _) => some (hd, ws, i2, pa2, m2, c2)

/-- Exact HOL `word_gen_gc_move_roots_bitmaps_def` (`stack_allocProofScript.sml:1842-1852`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGenGcMoveRootsBitmaps {width : Nat} {bitmapWidth : Nat} [NeZero width]
    [NeZero bitmapWidth] (conf : Config) :
    List (WordLocW width) × List (BitVec bitmapWidth) × BitVec width × BitVec width ×
        BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) ×
        (BitVec width → Bool) →
      List (WordLocW width) × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (stack, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) =>
      match encStack bitmaps stack with
      | none => (holArb _, holArb _, holArb _, holArb _, holArb _, holArb _, false)
      | some wlList =>
          let (wl, i2, pa2, ib2, pb2, m2, c2) :=
            wordGenGcMoveRoots conf (wlList, i1, pa1, ib1, pb1, curr, m, dm)
          match decStack bitmaps wl stack with
          | none => (holArb _, holArb _, holArb _, holArb _, holArb _, holArb _, false)
          | some stack => (stack, i2, pa2, ib2, pb2, m2, c2)

/-- Exact HOL `word_gen_gc_partial_move_roots_bitmaps_def`
(`stack_allocProofScript.sml:1854-1864`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGenGcPartialMoveRootsBitmaps {width : Nat} {bitmapWidth : Nat} [NeZero width]
    [NeZero bitmapWidth] (conf : Config) :
    List (WordLocW width) × List (BitVec bitmapWidth) × BitVec width × BitVec width ×
        BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width ×
        BitVec width →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) ×
        Bool
  | (stack, bitmaps, i1, pa1, curr, m, dm, gs, rs) =>
      match encStack bitmaps stack with
      | none => (holArb _, holArb _, holArb _, holArb _, false)
      | some wlList =>
          let (wl, i2, pa2, m2, c2) :=
            wordGenGcPartialMoveRoots conf (wlList, i1, pa1, curr, m, dm, gs, rs)
          match decStack bitmaps wl stack with
          | none => (holArb _, holArb _, holArb _, holArb _, false)
          | some stack => (stack, i2, pa2, m2, c2)

/-- Exact HOL `word_gen_gc_move_bitmaps_def` (`stack_allocProofScript.sml:1999-2013`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGenGcMoveBitmaps {descWidth : Nat} {width : Nat} {bitmapWidth : Nat} [NeZero descWidth]
    [NeZero width] [NeZero bitmapWidth] (conf : Config) :
    WordLocW descWidth × List (WordLocW width) × List (BitVec bitmapWidth) × BitVec width ×
        BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      Option (List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
        BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool)
  | (w, stack, bitmaps, i1, pa1, ib1, pb1, curr, m, dm) =>
      match fullReadBitmap bitmaps w with
      | none => none
      | some bs =>
          match filterBitmap bs stack with
          | none => none
          | some (ts, ws) =>
              let (wl, i2, pa2, ib2, pb2, m2, c2) :=
                wordGenGcMoveRoots conf (ts, i1, pa1, ib1, pb1, curr, m, dm)
              match mapBitmap bs wl stack with
              | none => none
              | some (hd, _, _) => some (hd, ws, i2, pa2, ib2, pb2, m2, c2)

/-- Exact HOL `word_gen_gc_partial_move_bitmaps_def` (`stack_allocProofScript.sml:2015-2029`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGenGcPartialMoveBitmaps {descWidth : Nat} {width : Nat} {bitmapWidth : Nat}
    [NeZero descWidth] [NeZero width] [NeZero bitmapWidth] (conf : Config) :
    WordLocW descWidth × List (WordLocW width) × List (BitVec bitmapWidth) × BitVec width ×
        BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) ×
        BitVec width × BitVec width →
      Option (List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool)
  | (w, stack, bitmaps, i1, pa1, curr, m, dm, gs, rs) =>
      match fullReadBitmap bitmaps w with
      | none => none
      | some bs =>
          match filterBitmap bs stack with
          | none => none
          | some (ts, ws) =>
              let (wl, i2, pa2, m2, c2) :=
                wordGenGcPartialMoveRoots conf (ts, i1, pa1, curr, m, dm, gs, rs)
              match mapBitmap bs wl stack with
              | none => none
              | some (hd, _, _) => some (hd, ws, i2, pa2, m2, c2)

/-- Exact HOL `word_gen_gc_move_bitmap_def` (`stack_allocProofScript.sml:2199-2210`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGenGcMoveBitmap {descWidth : Nat} {width : Nat} [NeZero descWidth]
    [NeZero width] (conf : Config) :
    BitVec descWidth × List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      Option (List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
        BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool)
  | (w, stack, i1, pa1, ib1, pb1, curr, m, dm) =>
      let bs := getBits w
      match filterBitmap bs stack with
      | none => none
      | some (ts, ws) =>
          let (wl, i2, pa2, ib2, pb2, m2, c2) :=
            wordGenGcMoveRoots conf (ts, i1, pa1, ib1, pb1, curr, m, dm)
          match mapBitmap bs wl stack with
          | none => none
          | some (hd, _) => some (hd, ws, i2, pa2, ib2, pb2, m2, c2)

/-- Exact HOL `word_gen_gc_partial_move_bitmap_def` (`stack_allocProofScript.sml:2212-2223`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def wordGenGcPartialMoveBitmap {descWidth : Nat} {width : Nat} [NeZero descWidth]
    [NeZero width] (conf : Config) :
    BitVec descWidth × List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      Option (List (WordLocW width) × List (WordLocW width) × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool)
  | (w, stack, i1, pa1, curr, m, dm, gs, rs) =>
      let bs := getBits w
      match filterBitmap bs stack with
      | none => none
      | some (ts, ws) =>
          let (wl, i2, pa2, m2, c2) :=
            wordGenGcPartialMoveRoots conf (ts, i1, pa1, curr, m, dm, gs, rs)
          match mapBitmap bs wl stack with
          | none => none
          | some (hd, _) => some (hd, ws, i2, pa2, m2, c2)

/-- Exact HOL `word_gc_move_loop_F` (`stack_allocProofScript.sml:538-546`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGcMoveLoop_F {width : Nat} [NeZero width] :
    ∀ (k : Nat) (conf : Config) (pb i pa old : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (c1 : Bool),
      wordGcMoveLoop k conf (pb, i, pa, old, m, dm, false) = (i1, pa1, m1, c1) → ¬ c1 = true := by
  intro k
  induction k with
  | zero =>
      intro conf pb i pa old m dm i1 pa1 m1 c1 h
      rw [wordGcMoveLoop] at h
      split at h <;> simp_all
  | succ k ih =>
      intro conf pb i pa old m dm i1 pa1 m1 c1 h
      rw [wordGcMoveLoop] at h
      split at h
      · simp_all
      · simp only [Nat.add_one_ne_zero, if_false, Bool.false_and, Nat.add_sub_cancel] at h
        split at h
        · exact ih _ _ _ _ _ _ _ _ _ _ _ h
        · generalize wordGcMoveList (width := width) conf _ = r at h
          obtain ⟨pb', i1', pa1', m1', c1'⟩ := r
          exact ih _ _ _ _ _ _ _ _ _ _ _ (by simpa using h)

/-- Exact HOL `word_gc_move_loop_ok` (`stack_allocProofScript.sml:548-552`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGcMoveLoop_ok {width : Nat} [NeZero width] {k : Nat} {conf : Config}
    {pb i pa old : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {c : Bool} {i1 pa1 : BitVec width} {m1 : BitVec width → WordLocW width} {c1 : Bool} :
    wordGcMoveLoop k conf (pb, i, pa, old, m, dm, c) = (i1, pa1, m1, c1) → c1 = true → c = true := by
  intro h h1
  cases c with
  | true => rfl
  | false => exact absurd h1 (wordGcMoveLoop_F _ _ _ _ _ _ _ _ _ _ _ _ h)

/-- Exact HOL `word_gen_gc_partial_move_ref_list_ok` (`stack_allocProofScript.sml:1866-1882`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcPartialMoveRefList_ok {width : Nat} [NeZero width] :
    ∀ (k : Nat) (rs re pb pa old : BitVec width) (m : BitVec width → WordLocW width)
      (i gs : BitVec width) (dm : BitVec width → Bool) (conf : Config) (c : Bool)
      (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width),
      wordGenGcPartialMoveRefList k conf (pb, i, pa, old, m, dm, c, gs, rs, re) =
        (i1, pa1, m1, true) → c = true := by
  intro k
  induction k with
  | zero =>
      intro rs re pb pa old m i gs dm conf c i1 pa1 m1 h
      rw [wordGenGcPartialMoveRefList] at h
      split at h <;> simp_all
  | succ k ih =>
      intro rs re pb pa old m i gs dm conf c i1 pa1 m1 h
      rw [wordGenGcPartialMoveRefList] at h
      split at h
      · simp_all
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h
        generalize wordGenGcPartialMoveList (width := width) conf _ = r at h
        obtain ⟨pb', i1', pa1', m1', c1'⟩ := r
        have := ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
        simp only [Bool.and_eq_true] at this
        exact this.1.1

theorem listRel_length {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : ListRel R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem wordGcMoveRoots_nil {width : Nat} [NeZero width] (conf : Config)
    (i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordGcMoveRoots conf ([], i, pa, old, m, dm) = ([], i, pa, m, true) := by
  rw [wordGcMoveRoots]

theorem wordGcMoveRoots_cons {width : Nat} [NeZero width] (conf : Config) (w : WordLocW width)
    (ws : List (WordLocW width)) (i pa old : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) :
    wordGcMoveRoots conf (w :: ws, i, pa, old, m, dm) =
      (let (w1, i1, pa1, m1, c1) := wordGcMove conf (w, i, pa, old, m, dm)
       let (ws2, i2, pa2, m2, c2) := wordGcMoveRoots conf (ws, i1, pa1, old, m1, dm)
       (w1 :: ws2, i2, pa2, m2, c1 && c2)) := by
  rw [wordGcMoveRoots]

/-- Exact HOL `word_gc_move_roots_APPEND` (`stack_allocProofScript.sml:629-644`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGcMoveRoots_APPEND {width : Nat} [NeZero width] {conf : Config}
    {curr : BitVec width} {dm : BitVec width → Bool} :
    ∀ (xs ys : List (WordLocW width)) (i1 pa1 : BitVec width) (m : BitVec width → WordLocW width),
      wordGcMoveRoots conf (xs ++ ys, i1, pa1, curr, m, dm) =
        let (ws1, i1, pa1, m1, c1) := wordGcMoveRoots conf (xs, i1, pa1, curr, m, dm)
        let (ws2, i2, pa2, m2, c2) := wordGcMoveRoots conf (ys, i1, pa1, curr, m1, dm)
        (ws1 ++ ws2, i2, pa2, m2, c1 && c2) := by
  intro xs
  induction xs with
  | nil =>
      intro ys i1 pa1 m
      simp only [List.nil_append, wordGcMoveRoots_nil, List.nil_append, Bool.true_and]
  | cons x xs ih =>
      intro ys i1 pa1 m
      simp only [List.cons_append, wordGcMoveRoots_cons]
      generalize wordGcMove conf (x, i1, pa1, curr, m, dm) = r
      obtain ⟨w1, i1', pa1', m1', c1'⟩ := r
      simp only [ih]
      generalize wordGcMoveRoots conf (xs, i1', pa1', curr, m1', dm) = r2
      obtain ⟨ws2, i2, pa2, m2, c2⟩ := r2
      generalize wordGcMoveRoots conf (ys, i2, pa2, curr, m2, dm) = r3
      obtain ⟨ws3, i3, pa3, m3, c3⟩ := r3
      simp [Bool.and_assoc]

/-- Exact HOL `word_gc_move_roots_IMP_LENGTH` (`stack_allocProofScript.sml:646-654`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGcMoveRoots_IMP_LENGTH {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (r0 r1 curr : BitVec width) (r2 : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (ys : List (WordLocW width)) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (c : Bool) (conf : Config),
      wordGcMoveRoots conf (xs, r0, r1, curr, r2, dm) = (ys, i2, pa2, m2, c) →
      ys.length = xs.length := by
  intro xs r0 r1 curr r2 dm ys i2 pa2 m2 c conf h
  have hr := wordGcMoveRoots_rootRel conf xs r0 r1 curr r2 dm
  rw [h] at hr
  exact (listRel_length hr).symm

theorem wordGenGcMoveRoots_nil {width : Nat} [NeZero width] (conf : Config)
    (i pa ib pb old : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) :
    wordGenGcMoveRoots conf ([], i, pa, ib, pb, old, m, dm) = ([], i, pa, ib, pb, m, true) := by
  rw [wordGenGcMoveRoots]

theorem wordGenGcMoveRoots_cons {width : Nat} [NeZero width] (conf : Config)
    (w : WordLocW width) (ws : List (WordLocW width)) (i pa ib pb old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordGenGcMoveRoots conf (w :: ws, i, pa, ib, pb, old, m, dm) =
      (let (w1, i1, pa1, ib, pb, m1, c1) := wordGenGcMove conf (w, i, pa, ib, pb, old, m, dm)
       let (ws2, i2, pa2, ib, pb, m2, c2) := wordGenGcMoveRoots conf (ws, i1, pa1, ib, pb, old, m1, dm)
       (w1 :: ws2, i2, pa2, ib, pb, m2, c1 && c2)) := by
  rw [wordGenGcMoveRoots]

theorem wordGenGcPartialMoveRoots_nil {width : Nat} [NeZero width] (conf : Config)
    (i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (gs rs : BitVec width) :
    wordGenGcPartialMoveRoots conf ([], i, pa, old, m, dm, gs, rs) = ([], i, pa, m, true) := by
  rw [wordGenGcPartialMoveRoots]

theorem wordGenGcPartialMoveRoots_cons {width : Nat} [NeZero width] (conf : Config)
    (w : WordLocW width) (ws : List (WordLocW width)) (i pa old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (gs rs : BitVec width) :
    wordGenGcPartialMoveRoots conf (w :: ws, i, pa, old, m, dm, gs, rs) =
      (let (w1, i1, pa1, m1, c1) := wordGenGcPartialMove conf (w, i, pa, old, m, dm, gs, rs)
       let (ws2, i2, pa2, m2, c2) :=
         wordGenGcPartialMoveRoots conf (ws, i1, pa1, old, m1, dm, gs, rs)
       (w1 :: ws2, i2, pa2, m2, c1 && c2)) := by
  rw [wordGenGcPartialMoveRoots]

/-- Exact HOL `word_gen_gc_move_roots_APPEND` (`stack_allocProofScript.sml:2031-2047`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcMoveRoots_APPEND {width : Nat} [NeZero width] {conf : Config}
    {curr : BitVec width} {dm : BitVec width → Bool} :
    ∀ (xs ys : List (WordLocW width)) (i1 pa1 ib1 pb1 : BitVec width)
      (m : BitVec width → WordLocW width),
      wordGenGcMoveRoots conf (xs ++ ys, i1, pa1, ib1, pb1, curr, m, dm) =
        let (ws1, i1, pa1, ib1, pb1, m1, c1) :=
          wordGenGcMoveRoots conf (xs, i1, pa1, ib1, pb1, curr, m, dm)
        let (ws2, i2, pa2, ib2, pb2, m2, c2) :=
          wordGenGcMoveRoots conf (ys, i1, pa1, ib1, pb1, curr, m1, dm)
        (ws1 ++ ws2, i2, pa2, ib2, pb2, m2, c1 && c2) := by
  intro xs
  induction xs with
  | nil =>
      intro ys i1 pa1 ib1 pb1 m
      simp only [List.nil_append, wordGenGcMoveRoots_nil, Bool.true_and]
  | cons x xs ih =>
      intro ys i1 pa1 ib1 pb1 m
      simp only [List.cons_append, wordGenGcMoveRoots_cons]
      generalize wordGenGcMove conf (x, i1, pa1, ib1, pb1, curr, m, dm) = r
      obtain ⟨w1, i1', pa1', ib', pb', m1', c1'⟩ := r
      simp only [ih]
      generalize wordGenGcMoveRoots conf (xs, i1', pa1', ib', pb', curr, m1', dm) = r2
      obtain ⟨ws2, i2, pa2, ib2, pb2, m2, c2⟩ := r2
      generalize wordGenGcMoveRoots conf (ys, i2, pa2, ib2, pb2, curr, m2, dm) = r3
      obtain ⟨ws3, i3, pa3, ib3, pb3, m3, c3⟩ := r3
      simp [Bool.and_assoc]

/-- Exact HOL `word_gen_gc_partial_move_roots_APPEND` (`stack_allocProofScript.sml:2049-2065`);
HOL's unused binders `ib1 pb1` are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcPartialMoveRoots_APPEND {width : Nat} [NeZero width] {conf : Config}
    {curr : BitVec width} {dm : BitVec width → Bool} {gs rs : BitVec width} :
    ∀ (xs ys : List (WordLocW width)) (i1 pa1 _ib1 _pb1 : BitVec width)
      (m : BitVec width → WordLocW width),
      wordGenGcPartialMoveRoots conf (xs ++ ys, i1, pa1, curr, m, dm, gs, rs) =
        let (ws1, i1, pa1, m1, c1) :=
          wordGenGcPartialMoveRoots conf (xs, i1, pa1, curr, m, dm, gs, rs)
        let (ws2, i2, pa2, m2, c2) :=
          wordGenGcPartialMoveRoots conf (ys, i1, pa1, curr, m1, dm, gs, rs)
        (ws1 ++ ws2, i2, pa2, m2, c1 && c2) := by
  intro xs
  induction xs with
  | nil =>
      intro ys i1 pa1 _ _ m
      simp only [List.nil_append, wordGenGcPartialMoveRoots_nil, Bool.true_and]
  | cons x xs ih =>
      intro ys i1 pa1 ib1 pb1 m
      simp only [List.cons_append, wordGenGcPartialMoveRoots_cons]
      generalize wordGenGcPartialMove conf (x, i1, pa1, curr, m, dm, gs, rs) = r
      obtain ⟨w1, i1', pa1', m1', c1'⟩ := r
      simp only [ih _ _ _ ib1 pb1]
      generalize wordGenGcPartialMoveRoots conf (xs, i1', pa1', curr, m1', dm, gs, rs) = r2
      obtain ⟨ws2, i2, pa2, m2, c2⟩ := r2
      generalize wordGenGcPartialMoveRoots conf (ys, i2, pa2, curr, m2, dm, gs, rs) = r3
      obtain ⟨ws3, i3, pa3, m3, c3⟩ := r3
      simp [Bool.and_assoc]

/-- Exact HOL `word_gen_gc_move_roots_IMP_LENGTH` (`stack_allocProofScript.sml:2067-2077`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcMoveRoots_IMP_LENGTH {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (r0 r1 r3 r4 curr : BitVec width)
      (r2 : BitVec width → WordLocW width) (dm : BitVec width → Bool)
      (ys : List (WordLocW width)) (i2 pa2 : BitVec width) (m2 : BitVec width → WordLocW width)
      (c : Bool) (conf : Config) (ib2 pb2 : BitVec width),
      wordGenGcMoveRoots conf (xs, r0, r1, r3, r4, curr, r2, dm) = (ys, i2, pa2, ib2, pb2, m2, c) →
      ys.length = xs.length := by
  intro xs r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf ib2 pb2 h
  have hr := wordGenGcMoveRoots_rootRel conf xs r0 r1 r3 r4 curr r2 dm
  rw [h] at hr
  exact (listRel_length hr).symm

/-- Exact HOL `word_gen_gc_partial_move_roots_IMP_LENGTH`
(`stack_allocProofScript.sml:2079-2089`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcPartialMoveRoots_IMP_LENGTH {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (r0 r1 r3 r4 curr : BitVec width)
      (r2 : BitVec width → WordLocW width) (dm : BitVec width → Bool)
      (ys : List (WordLocW width)) (i2 pa2 : BitVec width) (m2 : BitVec width → WordLocW width)
      (c : Bool) (conf : Config),
      wordGenGcPartialMoveRoots conf (xs, r0, r1, curr, r2, dm, r3, r4) = (ys, i2, pa2, m2, c) →
      ys.length = xs.length := by
  intro xs r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf h
  have hr := wordGenGcPartialMoveRoots_rootRel conf xs r0 r1 curr r2 dm r3 r4
  rw [h] at hr
  exact (listRel_length hr).symm

/-- Exact HOL `word_gc_move_bitmaps_LENGTH` (`stack_allocProofScript.sml:1311-1321`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGcMoveBitmaps_LENGTH {descWidth : Nat} {width : Nat} {bitmapWidth : Nat} [NeZero descWidth]
    [NeZero width] [NeZero bitmapWidth] {conf : Config} {w : WordLocW descWidth}
    {stack : List (WordLocW width)} {bitmaps : List (BitVec bitmapWidth)}
    {i pa curr : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {xs stack1 : List (WordLocW width)} {i1 pa1 : BitVec width}
    {m1 : BitVec width → WordLocW width} :
    wordGcMoveBitmaps conf (w, stack, bitmaps, i, pa, curr, m, dm) =
        some (xs, stack1, i1, pa1, m1, true) →
      stack.length = xs.length + stack1.length := by
  intro h
  simp only [wordGcMoveBitmaps] at h
  split at h
  · exact absurd h (by simp)
  · rename_i bs _
    split at h
    · exact absurd h (by simp)
    · rename_i ts ws hf
      generalize wordGcMoveRoots conf (ts, i, pa, curr, m, dm) = r at h
      obtain ⟨wl, i2, pa2, m2, c2⟩ := r
      split at h
      · exact absurd h (by simp)
      · rename_i hd _ _ hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        rw [filter_bitmap_IMP_LENGTH _ _ _ _ hf, map_bitmap_IMP_LENGTH _ _ _ _ _ hm]

/-- Exact HOL `word_gen_gc_move_bitmaps_LENGTH` (`stack_allocProofScript.sml:3134-3144`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcMoveBitmaps_LENGTH {descWidth : Nat} {width : Nat} {bitmapWidth : Nat} [NeZero descWidth]
    [NeZero width] [NeZero bitmapWidth] {conf : Config} {w : WordLocW descWidth}
    {stack : List (WordLocW width)} {bitmaps : List (BitVec bitmapWidth)}
    {i pa ib pb curr : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {xs stack1 : List (WordLocW width)} {i1 pa1 ib1 pb1 : BitVec width}
    {m1 : BitVec width → WordLocW width} :
    wordGenGcMoveBitmaps conf (w, stack, bitmaps, i, pa, ib, pb, curr, m, dm) =
        some (xs, stack1, i1, pa1, ib1, pb1, m1, true) →
      stack.length = xs.length + stack1.length := by
  intro h
  simp only [wordGenGcMoveBitmaps] at h
  split at h
  · exact absurd h (by simp)
  · rename_i bs _
    split at h
    · exact absurd h (by simp)
    · rename_i ts ws hf
      generalize wordGenGcMoveRoots conf (ts, i, pa, ib, pb, curr, m, dm) = r at h
      obtain ⟨wl, i2, pa2, ib2, pb2, m2, c2⟩ := r
      split at h
      · exact absurd h (by simp)
      · rename_i hd _ _ hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        rw [filter_bitmap_IMP_LENGTH _ _ _ _ hf, map_bitmap_IMP_LENGTH _ _ _ _ _ hm]

/-- Exact HOL `word_gen_gc_partial_move_bitmaps_LENGTH` (`stack_allocProofScript.sml:3146-3156`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGenGcPartialMoveBitmaps_LENGTH {descWidth : Nat} {width : Nat} {bitmapWidth : Nat}
    [NeZero descWidth] [NeZero width] [NeZero bitmapWidth] {conf : Config}
    {w : WordLocW descWidth} {stack : List (WordLocW width)} {bitmaps : List (BitVec bitmapWidth)}
    {i pa curr : BitVec width} {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {gs rs : BitVec width} {xs stack1 : List (WordLocW width)} {i1 pa1 : BitVec width}
    {m1 : BitVec width → WordLocW width} :
    wordGenGcPartialMoveBitmaps conf (w, stack, bitmaps, i, pa, curr, m, dm, gs, rs) =
        some (xs, stack1, i1, pa1, m1, true) →
      stack.length = xs.length + stack1.length := by
  intro h
  simp only [wordGenGcPartialMoveBitmaps] at h
  split at h
  · exact absurd h (by simp)
  · rename_i bs _
    split at h
    · exact absurd h (by simp)
    · rename_i ts ws hf
      generalize wordGenGcPartialMoveRoots conf (ts, i, pa, curr, m, dm, gs, rs) = r at h
      obtain ⟨wl, i2, pa2, m2, c2⟩ := r
      split at h
      · exact absurd h (by simp)
      · rename_i hd _ _ hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        rw [filter_bitmap_IMP_LENGTH _ _ _ _ hf, map_bitmap_IMP_LENGTH _ _ _ _ _ hm]

end Flapjack.Compiler.Backend.StackAlloc
