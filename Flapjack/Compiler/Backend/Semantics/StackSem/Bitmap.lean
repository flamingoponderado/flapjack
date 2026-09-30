import Flapjack.HolRef

/-! Exact list-level bitmap prerequisites from stackSemScript.sml:27-71.
    These definitions retain HOL's polymorphic element carrier and use List,
    not arrays. The exact StackSem evaluator and GC wiring remain open. -/

namespace Flapjack.StackSem

/-- Exact bitmap selection, retaining the unconsumed input suffix. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "filter_bitmap_def"]
def filterBitmap {α : Type} : List Bool → List α → Option (List α × List α)
  | [], values => some ([], values)
  | false :: bits, _ :: values => filterBitmap bits values
  | true :: bits, value :: values =>
      match filterBitmap bits values with
      | none => none
      | some (selected, rest) => some (value :: selected, rest)
  | _, _ => none

/-- Exact bitmap reconstruction, retaining both unconsumed suffixes. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "map_bitmap_def"]
def mapBitmap {α : Type} : List Bool → List α → List α → Option (List α × List α × List α)
  | [], moved, values => some ([], moved, values)
  | false :: bits, moved, value :: values =>
      match mapBitmap bits moved values with
      | none => none
      | some (mapped, restMoved, restValues) => some (value :: mapped, restMoved, restValues)
  | true :: bits, movedValue :: moved, _ :: values =>
      match mapBitmap bits moved values with
      | none => none
      | some (mapped, restMoved, restValues) => some (movedValue :: mapped, restMoved, restValues)
  | _, _, _ => none

/-- Exact HOL successful-filter remainder bound, with no bitmap validity premise. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "filter_bitmap_LENGTH"]
theorem filterBitmapLength {α : Type} :
    ∀ (bs : List Bool) (xs x y : List α), filterBitmap bs xs = some (x, y) → y.length ≤ xs.length := by
  intro bs
  induction bs with
  | nil =>
      intro xs x y h
      simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact Nat.le_refl _
  | cons b bs ih =>
      intro xs x y h
      cases xs with
      | nil => cases b <;> simp [filterBitmap] at h
      | cons v vs =>
          cases b with
          | false => exact Nat.le_trans (ih vs x y h) (Nat.le_succ _)
          | true =>
              cases hr : filterBitmap bs vs with
              | none => simp [filterBitmap, hr] at h
              | some pair =>
                  obtain ⟨selected, rest⟩ := pair
                  simp only [filterBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
                  have hb := ih vs selected rest hr
                  rw [h.2] at hb
                  exact Nat.le_trans hb (Nat.le_succ _)

/-- Exact HOL reconstruction remainder bounds on both input lists. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "map_bitmap_LENGTH"]
theorem mapBitmapLength {α : Type} :
    ∀ (t1 : List Bool) (t2 t3 x y z : List α), mapBitmap t1 t2 t3 = some (x, y, z) →
      y.length ≤ t2.length ∧ z.length ≤ t3.length := by
  intro bits
  induction bits with
  | nil =>
      intro moved values x y z h
      simp only [mapBitmap, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1, ← h.2.2]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons b bits ih =>
      intro moved values x y z h
      cases values with
      | nil => cases b <;> cases moved <;> simp [mapBitmap] at h
      | cons v vs =>
          cases b with
          | false =>
              cases hr : mapBitmap bits moved vs with
              | none => simp [mapBitmap, hr] at h
              | some pair =>
                  obtain ⟨mapped, restMoved, restValues⟩ := pair
                  simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
                  have hb := ih moved vs mapped restMoved restValues hr
                  rw [h.2.1, h.2.2] at hb
                  exact ⟨hb.1, Nat.le_trans hb.2 (Nat.le_succ _)⟩
          | true =>
              cases moved with
              | nil => simp [mapBitmap] at h
              | cons m ms =>
                  cases hr : mapBitmap bits ms vs with
                  | none => simp [mapBitmap, hr] at h
                  | some pair =>
                      obtain ⟨mapped, restMoved, restValues⟩ := pair
                      simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
                      have hb := ih ms vs mapped restMoved restValues hr
                      rw [h.2.1, h.2.2] at hb
                      exact ⟨Nat.le_trans hb.1 (Nat.le_succ _), Nat.le_trans hb.2 (Nat.le_succ _)⟩

end Flapjack.StackSem
