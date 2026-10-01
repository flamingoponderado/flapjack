import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Compiler.Backend.RegAlloc.SpDefault
import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Literal total colouring lookup. Missing physical registers retain their
original key; other missing registers map to zero. Every mapped value is doubled. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "total_colour_def"]
def totalColour (colour : Spt Nat) (register : Nat) : Nat :=
  match sptLookup register colour with
  | none => if isPhyVar register then register else 0
  | some value => 2 * value

/-- Exact HOL `total_colour_alt` (`word_allocScript.sml:1597-1604`): the total
colouring doubles `sp_default`. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "total_colour_alt"]
theorem totalColourAlt (col : Spt Nat) : totalColour col = (fun x => 2 * x) ∘ spDefault col := by
  funext x
  simp only [totalColour, spDefault, Function.comp]
  cases sptLookup x col with
  | some v => rfl
  | none =>
    by_cases h : isPhyVar x = true
    · simp only [h, if_true]
      simp [isPhyVar] at h
      omega
    · simp [h]

end Flapjack.WordAlloc
