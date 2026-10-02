import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack.StackSem

/-- Full original constructive bitmap mapping success and re-filtering result.
The original existential z is omitted after source review: it occurs neither
in either conclusion conjunct nor in any hypothesis. No mapped target success
or additional bitmap/input length premise is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_success"]
theorem mapBitmapSuccess {α : Type} (bs : List Bool) (stack a b ls : List α)
    (hf : filterBitmap bs stack = some (a, b)) (hlen : ls.length = a.length) :
    ∃ x, mapBitmap bs ls stack = some (x, [], stack.drop bs.length) ∧
      filterBitmap bs x = some (ls, []) := by
  induction bs generalizing stack a b ls with
  | nil =>
    simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at hf
    have hl : ls = [] := by cases ls <;> simp_all
    subst ls
    exact ⟨[], rfl, rfl⟩
  | cons bit bs ih =>
    cases stack with
    | nil => cases bit <;> simp [filterBitmap] at hf
    | cons v vs =>
      cases bit with
      | false =>
        obtain ⟨x, hm, hx⟩ := ih vs a b ls hf hlen
        refine ⟨v :: x, ?_, ?_⟩
        · simp [mapBitmap, hm]
        · exact hx
      | true =>
        cases hr : filterBitmap bs vs with
        | none => simp [filterBitmap, hr] at hf
        | some pair =>
          rcases pair with ⟨selected, rest⟩
          simp only [filterBitmap, hr, Option.some.injEq, Prod.mk.injEq] at hf
          cases ls with
          | nil => simp [← hf.1] at hlen
          | cons m ms =>
            have hl : ms.length = selected.length := by simpa [← hf.1] using hlen
            obtain ⟨x, hm, hx⟩ := ih vs selected rest ms hr hl
            refine ⟨m :: x, ?_, ?_⟩
            · simp [mapBitmap, hm]
            · simp [filterBitmap, hx]

/-- Full original extension by an arbitrary unused replacement suffix. The
original universally quantified n is omitted: it occurs nowhere in the source
hypothesis or conclusion and is vacuous for this complete theorem. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_more"]
theorem mapBitmapMore {α : Type} (bs : List Bool) (ls stack a c ls' : List α)
    (h : mapBitmap bs ls stack = some (a, [], c)) :
    mapBitmap bs (ls ++ ls') stack = some (a, ls', c) := by
  induction bs generalizing ls stack a c with
  | nil =>
    simp only [mapBitmap, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨ha, hl, hc⟩
    subst ls
    simp [mapBitmap, ← ha, ← hc]
  | cons bit bs ih =>
    cases stack with
    | nil => cases bit <;> cases ls <;> simp [mapBitmap] at h
    | cons v vs =>
      cases bit with
      | false =>
        cases hr : mapBitmap bs ls vs with
        | none => simp [mapBitmap, hr] at h
        | some result =>
          rcases result with ⟨mapped, movedRest, stackRest⟩
          simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨ha, hl, hc⟩
          have hm := ih ls vs mapped stackRest (by simpa [hl] using hr)
          simp [mapBitmap, hm, ha, hc]
      | true =>
        cases ls with
        | nil => simp [mapBitmap] at h
        | cons m ms =>
          cases hr : mapBitmap bs ms vs with
          | none => simp [mapBitmap, hr] at h
          | some result =>
            rcases result with ⟨mapped, movedRest, stackRest⟩
            simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨ha, hl, hc⟩
            have hm := ih ms vs mapped stackRest (by simpa [hl] using hr)
            simp [mapBitmap, hm, ha, hc]

/-- Full original arbitrary-list-length prefix/suffix specialization. The
original l is retained at an independent payload type since its length matters. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_more_simp"]
theorem mapBitmapMoreSimp {α β : Type} (bs : List Bool) (l : List β)
    (ls stack a c : List α)
    (h : mapBitmap bs (ls.take l.length) stack = some (a, [], c)) :
    mapBitmap bs ls stack = some (a, ls.drop l.length, c) := by
  simpa only [List.take_append_drop] using
    mapBitmapMore bs (ls.take l.length) stack a c (ls.drop l.length) h

/-- Full original preservation of a false-mask slot using optional HOL oEL
lookup, represented by getElem?. No total EL, extra bound, or default is used. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_LLOOKUP_F"]
theorem mapBitmapLookupFalse {α : Type} (bm : List Bool) (ls stack : List α) (n : Nat)
    (res ls1 stack1 : List α) (hb : bm[n]? = some false)
    (hm : mapBitmap bm ls stack = some (res, ls1, stack1)) :
    ∃ v, res[n]? = some v ∧ stack[n]? = some v := by
  induction bm generalizing ls stack n res ls1 stack1 with
  | nil => simp at hb
  | cons bit bs ih =>
    cases stack with
    | nil => cases bit <;> cases ls <;> simp [mapBitmap] at hm
    | cons v vs =>
      cases bit with
      | false =>
        cases hr : mapBitmap bs ls vs with
        | none => simp [mapBitmap, hr] at hm
        | some result =>
          rcases result with ⟨mapped, movedRest, stackRest⟩
          simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at hm
          rcases hm with ⟨hres, _, _⟩
          cases n with
          | zero => exact ⟨v, by simp [← hres], rfl⟩
          | succ n =>
            have hb' : bs[n]? = some false := by simpa using hb
            obtain ⟨w, hw, hv⟩ := ih ls vs n mapped movedRest stackRest hb' hr
            exact ⟨w, by simpa [← hres] using hw, by simpa using hv⟩
      | true =>
        cases ls with
        | nil => simp [mapBitmap] at hm
        | cons m ms =>
          cases hr : mapBitmap bs ms vs with
          | none => simp [mapBitmap, hr] at hm
          | some result =>
            rcases result with ⟨mapped, movedRest, stackRest⟩
            simp only [mapBitmap, hr, Option.some.injEq, Prod.mk.injEq] at hm
            rcases hm with ⟨hres, _, _⟩
            cases n with
            | zero => simp at hb
            | succ n =>
              have hb' : bs[n]? = some false := by simpa using hb
              obtain ⟨w, hw, hv⟩ := ih ms vs n mapped movedRest stackRest hb' hr
              exact ⟨w, by simpa [← hres] using hw, by simpa using hv⟩

end Flapjack.Compiler.Backend.WordToStack
