import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexListLemmas
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack.StackSem

/-- Flapjack induction infrastructure for the native bitmap selector. No separate
HOL declaration is attached to this unconditional closed-form helper. -/
private theorem filterBitmapFormula {α : Type} (bs : List Bool) (xs : List α) :
    filterBitmap bs xs = if bs.length ≤ xs.length then
      some (((xs.zip bs).filter (fun p => p.2)).map Prod.fst, xs.drop bs.length)
    else none := by
  induction bs generalizing xs with
  | nil => simp [filterBitmap]
  | cons b bs ih =>
    cases xs with
    | nil => cases b <;> simp [filterBitmap]
    | cons x xs =>
      cases b <;> simp [filterBitmap, ih] <;> split <;> simp_all

/-- Full original equal-length zip/filter reconstruction. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IMP_filter_bitmap_EQ_SOME_NIL"]
theorem filterBitmapEqSomeNil {α : Type} (xs : List Bool) (ys zs : List α)
    (hlen : xs.length = ys.length)
    (hz : zs = ((ys.zip xs).filter (fun p => p.2)).map Prod.fst) :
    filterBitmap xs ys = some (zs, []) := by
  rw [filterBitmapFormula, if_pos (by omega), ← hz]
  simp [hlen]

/-- Full original selected-list length bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_length"]
theorem filterBitmapSelectedLength {α : Type} (bs : List Bool) (ls xs ys : List α)
    (h : filterBitmap bs ls = some (xs, ys)) : xs.length ≤ bs.length := by
  rw [filterBitmapFormula] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, List.length_map]
    exact Nat.le_trans (List.length_filter_le ..) (by rw [List.length_zip]; exact Nat.min_le_right ..)
  · contradiction

/-- Full original successful-input length bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_length_input"]
theorem filterBitmapInputLength {α : Type} (xs : List Bool) (ys : List α)
    (ls : List α × List α) (h : filterBitmap xs ys = some ls) :
    xs.length ≤ ys.length := by
  rw [filterBitmapFormula] at h
  split at h
  · assumption
  · contradiction

/-- Flapjack structural map transport used to prove the original projection laws;
no separate HOL declaration is attached to this arbitrary-function helper. -/
private theorem filterBitmapMap {α β : Type} (f : α → β) (bs : List Bool) (xs : List α) :
    filterBitmap bs (xs.map f) =
      (filterBitmap bs xs).map (fun (a, b) => (a.map f, b.map f)) := by
  induction bs generalizing xs with
  | nil => simp [filterBitmap]
  | cons b bs ih =>
    cases xs with
    | nil => cases b <;> simp [filterBitmap]
    | cons x xs =>
      cases b with
      | false => simpa [filterBitmap] using ih xs
      | true =>
        simp only [List.map_cons, filterBitmap, ih]
        cases filterBitmap bs xs <;> simp

/-- Flapjack pair-list extensionality helper. No separate HOL original. -/
private theorem pairListExt {α β : Type} (xs ys : List (α × β))
    (hf : xs.map Prod.fst = ys.map Prod.fst)
    (hs : xs.map Prod.snd = ys.map Prod.snd) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hf
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hf hs
      have hxy : x = y := Prod.ext hf.1 hs.1
      rw [hxy, ih ys hf.2 hs.2]

/-- Full original pair reconstruction from both successful projection filters. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_MAP_IMP"]
theorem filterBitmapPairReconstruct {α β : Type} (ys : List Bool) (xs l : List (α × β))
    (hs : filterBitmap ys (xs.map Prod.snd) = some (l.map Prod.snd, []))
    (hf : filterBitmap ys (xs.map Prod.fst) = some (l.map Prod.fst, [])) :
    filterBitmap ys xs = some (l, []) := by
  rw [filterBitmapMap] at hs hf
  cases he : filterBitmap ys xs with
  | none => simp [he] at hs
  | some pair =>
    rcases pair with ⟨selected, rest⟩
    simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs hf
    have hr : rest = [] := by simpa using hs.2
    have hl := pairListExt selected l hf.1 hs.1
    rw [hr, hl]

/-- Full original successful SND projection transport. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_IMP_MAP_SND"]
theorem filterBitmapMapSnd {α β : Type} (ys : List Bool) (xs l : List (α × β))
    (h : filterBitmap ys xs = some (l, [])) :
    filterBitmap ys (xs.map Prod.snd) = some (l.map Prod.snd, []) := by
  rw [filterBitmapMap, h]
  rfl

/-- Full original successful FST projection transport. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_IMP_MAP_FST"]
theorem filterBitmapMapFst {α β : Type} (ys : List Bool) (xs l : List (α × β))
    (h : filterBitmap ys xs = some (l, [])) :
    filterBitmap ys (xs.map Prod.fst) = some (l.map Prod.fst, []) := by
  rw [filterBitmapMap, h]
  rfl

/-- Flapjack structural helper retaining selected values while discarding
only the suffix outside the bitmap. No separate HOL original. -/
private theorem filterBitmapTake {α : Type} (bs : List Bool) (xs : List α) :
    filterBitmap bs (xs.take bs.length) =
      (filterBitmap bs xs).map (fun (selected, _) => (selected, [])) := by
  induction bs generalizing xs with
  | nil => simp [filterBitmap]
  | cons b bs ih =>
    cases xs with
    | nil => cases b <;> simp [filterBitmap]
    | cons x xs =>
      cases b with
      | false => simpa [filterBitmap] using ih xs
      | true =>
        simp only [List.length_cons, List.take_succ_cons, filterBitmap, ih]
        cases filterBitmap bs xs <;> simp

/-- Flapjack success-result suffix identification, derived from the native
selector rather than assumed. No separate HOL original. -/
private theorem filterBitmapRest {α : Type} (bs : List Bool) (xs selected rest : List α)
    (h : filterBitmap bs xs = some (selected, rest)) : rest = xs.drop bs.length := by
  rw [filterBitmapFormula] at h
  split at h
  · exact (Prod.mk.inj (Option.some.inj h)).2.symm
  · contradiction

/-- Full original successful prefix selection extended with its exact suffix. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_TAKE_LENGTH_IMP"]
theorem filterBitmapTakeLength {α β : Type} (h5 : List Bool) (x4 : List α)
    (l : List (β × α))
    (h : filterBitmap h5 (x4.take h5.length) = some (l.map Prod.snd, [])) :
    filterBitmap h5 x4 = some (l.map Prod.snd, x4.drop h5.length) := by
  rw [filterBitmapTake] at h
  cases he : filterBitmap h5 x4 with
  | none => simp [he] at h
  | some pair =>
    rcases pair with ⟨selected, rest⟩
    have hr := filterBitmapRest h5 x4 selected rest he
    simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1, hr]

/-- Full original indexed-prefix bitmap reconstruction. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_lemma"]
theorem filterBitmapIndexReconstruct {α : Type} (h5 : List Bool) (x4 : List α)
    (k : Nat) (l : List (Nat × α))
    (h : filterBitmap h5 (Flapjack.WordToStackProofs.indexList (x4.take h5.length) k) =
      some (l, [])) :
    filterBitmap h5 x4 = some (l.map Prod.snd, x4.drop h5.length) := by
  have hm := filterBitmapMapSnd h5 _ l h
  rw [Flapjack.WordToStackProofs.mapSndIndexList] at hm
  exact filterBitmapTakeLength h5 x4 l hm

/-- Full original selected-value membership in the input list. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_MEM"]
theorem filterBitmapMem {α : Type} (b : List Bool) (ls ls' : List α) (x : α)
    (h : filterBitmap b ls = some (ls', [])) (hx : x ∈ ls') : x ∈ ls := by
  rw [filterBitmapFormula] at h
  split at h
  · have hs := (Prod.mk.inj (Option.some.inj h)).1
    rw [← hs] at hx
    obtain ⟨pair, hp, he⟩ := List.mem_map.mp hx
    have hz := (List.mem_filter.mp hp).1
    have hm := (List.of_mem_zip hz).1
    simpa [he] using hm
  · contradiction

end Flapjack.Compiler.Backend.WordToStack
