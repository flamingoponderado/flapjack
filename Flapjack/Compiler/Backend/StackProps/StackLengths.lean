import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec

/-! Full original StackProps bitmap reconstruction and stack length chain.
Generic reconstruction payloads are unchanged; stack decoding retains the
independent bitmap and stack word dimensions and original success premise. -/
namespace Flapjack.StackPropsStackLengths
open StackSem

/-- Full original two reconstruction length equations, over arbitrary payloads. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "map_bitmap_length"]
theorem mapBitmapLengths {α : Type} :
    ∀ (bits : List Bool) (roots values front remainingRoots remainder : List α),
      mapBitmap bits roots values = some (front, remainingRoots, remainder) →
      values.length = front.length + remainder.length ∧ front.length = bits.length := by
  intro bits
  induction bits with
  | nil =>
      intro roots values front remainingRoots remainder h
      simp only [mapBitmap, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp
  | cons bit bits ih =>
      intro roots values front remainingRoots remainder h
      cases values with
      | nil => cases bit <;> cases roots <;> simp [mapBitmap] at h
      | cons value values =>
          cases bit with
          | false =>
              cases hr : mapBitmap bits roots values with
              | none => simp [mapBitmap, hr] at h
              | some result =>
                  rcases result with ⟨mapped, restRoots, restValues⟩
                  simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl, rfl⟩
                  have hi := ih roots values mapped restRoots restValues hr
                  simp only [List.length_cons]
                  omega
          | true =>
              cases roots with
              | nil => simp [mapBitmap] at h
              | cons root roots =>
                  cases hr : mapBitmap bits roots values with
                  | none => simp [mapBitmap, hr] at h
                  | some result =>
                      rcases result with ⟨mapped, restRoots, restValues⟩
                      simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl, rfl⟩
                      have hi := ih roots values mapped restRoots restValues hr
                      simp only [List.length_cons]
                      omega

/-- Full original decoded-stack length, with independent bitmap/stack widths. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "dec_stack_length"
  (words_as_type_indexed_bitvec)]
theorem decStackLength {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth)) (roots stack decoded : List (WordLocW width))
    (h : decStack bitmaps roots stack = some decoded) :
    stack.length = decoded.length := by
  generalize hn : stack.length = n
  induction n using Nat.strongRecOn generalizing roots stack decoded with
  | ind n ih =>
      cases stack with
      | nil => simp [decStack] at h
      | cons header tail =>
          rw [decStack] at h
          split at h
          · split at h
            · simp only [Option.some.injEq] at h
              subst decoded
              rename_i hz
              simp_all
            · simp at h
          · split at h
            · simp at h
            · rename_i bits hbits
              split at h
              · simp at h
              · rename_i front restRoots restValues hm
                split at h
                · simp at h
                · rename_i rest hd
                  simp only [Option.some.injEq] at h
                  subst decoded
                  have lengths := mapBitmapLengths bits roots tail front restRoots restValues hm
                  have bound := (mapBitmapLength bits roots tail front restRoots restValues hm).2
                  have recLength := ih restValues.length (by simp only [List.length_cons] at hn; omega)
                    restRoots restValues rest hd rfl
                  simp only [List.length_cons, List.length_append, List.length_nil] at hn ⊢
                  omega

end Flapjack.StackPropsStackLengths
