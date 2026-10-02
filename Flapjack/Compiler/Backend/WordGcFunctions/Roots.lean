import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Compiler.Backend.WordSimp.Proofs.GcWordConst
import Flapjack.Pancake.Semantics.PanSem.DecCallExact

/-!
# `word_gcFunctions` root theorems

The `EVERY2`/`LENGTH` theorems of
`cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml:504-598`: every
collector keeps the word/location kind of each root and leaves GC constants
unchanged, so `word_gc_fun` preserves the root count.  HOL `EVERY2`
(`LIST_REL`) is the exact inductive rendering `Flapjack.ListRel`.
-/

namespace Flapjack.Compiler.Backend.WordGcFunctions

open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordSimp

/-- The root relation of the `*_IMP_EVERY2` theorems (Flapjack abbreviation of
HOL's inline lambda). -/
abbrev gcRootRel {width : Nat} [NeZero width] (x y : WordLocW width) : Prop :=
  (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧ (isGcWordConst x = true → x = y)

theorem wordGcMove_rootRel {width : Nat} [NeZero width] (conf : Config)
    (x : WordLocW width) (i pa old : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) :
    gcRootRel x (wordGcMove conf (x, i, pa, old, m, dm)).1 := by
  cases x with
  | loc l1 l2 => simp [wordGcMove, gcRootRel]
  | word w =>
      simp only [wordGcMove]
      repeat' split
      all_goals simp_all [gcRootRel, wordSemIsWordLoc, isGcWordConst, isGcConst]

theorem wordGenGcPartialMove_rootRel {width : Nat} [NeZero width] (conf : Config)
    (x : WordLocW width) (i pa old : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (gs rs : BitVec width) :
    gcRootRel x (wordGenGcPartialMove conf (x, i, pa, old, m, dm, gs, rs)).1 := by
  cases x with
  | loc l1 l2 => simp [wordGenGcPartialMove, gcRootRel]
  | word w =>
      simp only [wordGenGcPartialMove]
      repeat' split
      all_goals simp_all [gcRootRel, wordSemIsWordLoc, isGcWordConst, isGcConst]

theorem wordGenGcMove_rootRel {width : Nat} [NeZero width] (conf : Config)
    (x : WordLocW width) (i pa ib pb old : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) :
    gcRootRel x (wordGenGcMove conf (x, i, pa, ib, pb, old, m, dm)).1 := by
  cases x with
  | loc l1 l2 => simp [wordGenGcMove, gcRootRel]
  | word w =>
      have hc : (1 : BitVec width) &&& w = w &&& 1 := BitVec.and_comm _ _
      simp only [wordGenGcMove, hc]
      repeat' split
      all_goals simp_all [gcRootRel, wordSemIsWordLoc, isGcWordConst, isGcConst]

theorem wordGcMoveRoots_rootRel {width : Nat} [NeZero width] (c : Config) :
    ∀ (xs : List (WordLocW width)) (i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool),
      ListRel gcRootRel xs ((wordGcMoveRoots c (xs, i, pa, old, m, dm)).1)
  | [], i, pa, old, m, dm => by simp [wordGcMoveRoots]; exact .nil
  | x :: xs, i, pa, old, m, dm => by
      simp only [wordGcMoveRoots]
      exact .cons (wordGcMove_rootRel c x i pa old m dm) (wordGcMoveRoots_rootRel c xs _ _ _ _ _)

/-- Exact HOL `word_gc_move_roots_IMP_EVERY2` (`word_gcFunctionsScript.sml:504-521`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gc_move_roots_IMP_EVERY2" (words_as_type_indexed_bitvec)]
theorem wordGcMoveRoots_IMP_EVERY2 {width : Nat} [NeZero width] :
    ∀ (xs ys : List (WordLocW width)) (pa : BitVec width) (m : BitVec width → WordLocW width)
      (i : BitVec width) (c1 : Bool) (m1 : BitVec width → WordLocW width)
      (pa1 i1 old : BitVec width) (dm : BitVec width → Bool) (c : Config),
      wordGcMoveRoots c (xs, i, pa, old, m, dm) = (ys, i1, pa1, m1, c1) →
      ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (isGcWordConst x = true → x = y)) xs ys := by
  intro xs ys pa m i c1 m1 pa1 i1 old dm c h
  have hr := wordGcMoveRoots_rootRel c xs i pa old m dm
  rw [h] at hr
  exact hr

theorem wordGenGcMoveRoots_rootRel {width : Nat} [NeZero width] (c : Config) :
    ∀ (xs : List (WordLocW width)) (i pa ib pb old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool),
      ListRel gcRootRel xs ((wordGenGcMoveRoots c (xs, i, pa, ib, pb, old, m, dm)).1)
  | [], i, pa, ib, pb, old, m, dm => by simp [wordGenGcMoveRoots]; exact .nil
  | x :: xs, i, pa, ib, pb, old, m, dm => by
      simp only [wordGenGcMoveRoots]
      exact .cons (wordGenGcMove_rootRel c x i pa ib pb old m dm) (wordGenGcMoveRoots_rootRel c xs _ _ _ _ _ _ _)

/-- Exact HOL `word_gen_gc_move_roots_IMP_EVERY2` (`word_gcFunctionsScript.sml:523-543`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_move_roots_IMP_EVERY2" (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRoots_IMP_EVERY2 {width : Nat} [NeZero width] :
    ∀ (xs ys : List (WordLocW width)) (pa : BitVec width) (m : BitVec width → WordLocW width)
      (i ib pb : BitVec width) (c1 : Bool) (m1 : BitVec width → WordLocW width)
      (pa1 i1 ib1 pb1 old : BitVec width) (dm : BitVec width → Bool) (c : Config),
      wordGenGcMoveRoots c (xs, i, pa, ib, pb, old, m, dm) = (ys, i1, pa1, ib1, pb1, m1, c1) →
      ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (isGcWordConst x = true → x = y)) xs ys := by
  intro xs ys pa m i ib pb c1 m1 pa1 i1 ib1 pb1 old dm c h
  have hr := wordGenGcMoveRoots_rootRel c xs i pa ib pb old m dm
  rw [h] at hr
  exact hr

theorem wordGenGcPartialMoveRoots_rootRel {width : Nat} [NeZero width] (c : Config) :
    ∀ (xs : List (WordLocW width)) (i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (gs rs : BitVec width),
      ListRel gcRootRel xs ((wordGenGcPartialMoveRoots c (xs, i, pa, old, m, dm, gs, rs)).1)
  | [], i, pa, old, m, dm, gs, rs => by simp [wordGenGcPartialMoveRoots]; exact .nil
  | x :: xs, i, pa, old, m, dm, gs, rs => by
      simp only [wordGenGcPartialMoveRoots]
      exact .cons (wordGenGcPartialMove_rootRel c x i pa old m dm gs rs) (wordGenGcPartialMoveRoots_rootRel c xs _ _ _ _ _ _ _)

/-- Exact HOL `word_gen_gc_partial_move_roots_IMP_EVERY2`
(`word_gcFunctionsScript.sml:545-566`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_roots_IMP_EVERY2" (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRoots_IMP_EVERY2 {width : Nat} [NeZero width] :
    ∀ (xs ys : List (WordLocW width)) (pa : BitVec width) (m : BitVec width → WordLocW width)
      (i gs rs : BitVec width) (c1 : Bool) (m1 : BitVec width → WordLocW width)
      (pa1 i1 old : BitVec width) (dm : BitVec width → Bool) (c : Config),
      wordGenGcPartialMoveRoots c (xs, i, pa, old, m, dm, gs, rs) = (ys, i1, pa1, m1, c1) →
      ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (isGcWordConst x = true → x = y)) xs ys := by
  intro xs ys pa m i gs rs c1 m1 pa1 i1 old dm c h
  have hr := wordGenGcPartialMoveRoots_rootRel c xs i pa old m dm gs rs
  rw [h] at hr
  exact hr

theorem wordFullGc_fst {width : Nat} [NeZero width] (c : Config) (r : List (WordLocW width))
    (new old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    (wordFullGc c (r, new, old, m, dm)).1 = (wordGcMoveRoots c (r, 0, new, old, m, dm)).1 := by
  simp only [wordFullGc]

theorem wordGenGcPartialFull_fst {width : Nat} [NeZero width] (c : Config)
    (r : List (WordLocW width)) (curr new len : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (gs rs : BitVec width) :
    (wordGenGcPartialFull c (r, curr, new, len, m, dm, gs, rs)).1 =
      (wordGenGcPartialMoveRoots c (r, gs >>> wordShiftAmount width, new, curr, m, dm, gs, rs)).1 := by
  simp only [wordGenGcPartialFull, wordGenGcPartial]

theorem wordGenGc_fst {width : Nat} [NeZero width] (c : Config) (r : List (WordLocW width))
    (curr new len : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    (wordGenGc c (r, curr, new, len, m, dm)).1 =
      (wordGenGcMoveRoots c (r, 0, new, len >>> wordShiftAmount width, new + len, curr, m, dm)).1 := by
  simp only [wordGenGc]

/-- Exact HOL `word_gc_IMP_EVERY2` (`word_gcFunctionsScript.sml:568-589`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_IMP_EVERY2"
  (fmap_as_finite_support_relation := [st, s1]) (words_as_type_indexed_bitvec)]
theorem word_gc_IMP_EVERY2 {width : Nat} [NeZero width] {c : Config}
    {xs ys : List (WordLocW width)} {m m1 : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {st : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {s1 : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    wordGcFun c (xs, m, dm, st) = some (ys, m1, s1) →
    ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
      (isGcWordConst x = true → x = y)) xs ys := by
  intro h
  have tailRel : ∀ (g : WordLocW width) (zs : List (WordLocW width)),
      ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (isGcWordConst x = true → x = y)) (g :: xs) zs →
      ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (isGcWordConst x = true → x = y)) xs zs.tail := by
    intro g zs hz
    cases hz with
    | cons _ hrest => exact hrest
  have refl : ∀ zs : List (WordLocW width), ListRel gcRootRel zs zs := by
    intro zs
    induction zs with
    | nil => exact .nil
    | cons z zs ih => exact .cons ⟨rfl, fun _ => rfl⟩ ih
  simp only [wordGcFun] at h
  cases hk : c.gcKind with
  | none =>
      simp only [hk] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact refl xs
      · exact absurd h (by simp)
  | simple =>
      simp only [hk] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        apply tailRel
        rw [wordFullGc_fst]
        exact wordGcMoveRoots_rootRel c _ _ _ _ _ _
      · exact absurd h (by simp)
  | generational genSizes =>
      simp only [hk] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            apply tailRel
            rw [wordGenGcPartialFull_fst]
            exact wordGenGcPartialMoveRoots_rootRel c _ _ _ _ _ _ _ _
          · exact absurd h (by simp)
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            apply tailRel
            rw [wordGenGc_fst]
            exact wordGenGcMoveRoots_rootRel c _ _ _ _ _ _ _ _
          · exact absurd h (by simp)

/-- Exact HOL `word_gc_fun_LENGTH` (`word_gcFunctionsScript.sml:591-596`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_LENGTH"
  (fmap_as_finite_support_relation := [s, s1]) (words_as_type_indexed_bitvec)]
theorem word_gc_fun_LENGTH {width : Nat} [NeZero width] {c : Config}
    {xs zs : List (WordLocW width)} {m m1 : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {s : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {s1 : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    wordGcFun c (xs, m, dm, s) = some (zs, m1, s1) → xs.length = zs.length := by
  intro h
  have hr := word_gc_IMP_EVERY2 h
  clear h
  induction hr with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end Flapjack.Compiler.Backend.WordGcFunctions
