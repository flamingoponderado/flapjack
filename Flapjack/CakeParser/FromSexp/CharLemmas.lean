module

public import Flapjack.HolRef
public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-!
# `fromSexp` character-class facts

Ports of `cakeml/compiler/parsing/fromSexpScript.sml:207-217`: the
`isAlpha`/`isUpper`/`isLower` character tests from HOL's `stringScript.sml`
(rendered and tagged in `Flapjack.Basis.Pure.MlString`) are exclusive, and
lower case implies alphabetic.
-/

namespace Flapjack.CakeParser.FromSexp

open Flapjack.Basis.Pure.MlString

/-- Original `isAlpha_isUpper_isLower`: an alphabetic character is upper or
lower but never both. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "isAlpha_isUpper_isLower"]
theorem isAlpha_isUpper_isLower (c : HolChar) (h : isAlphaChar c = true) :
    isUpperChar c ≠ isLowerChar c := by
  intro heq
  rcases (by simpa [isAlphaChar, Bool.or_eq_true] using h) with hl | hu
  · have hu : isUpperChar c = true := heq ▸ hl
    simp only [isLowerChar, isUpperChar, Bool.and_eq_true, decide_eq_true_eq] at hl hu
    omega
  · have hl : isLowerChar c = true := heq ▸ hu
    simp only [isLowerChar, isUpperChar, Bool.and_eq_true, decide_eq_true_eq] at hl hu
    omega

/-- Original `isLower_isAlpha`: a lower-case character is alphabetic. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "isLower_isAlpha"]
theorem isLower_isAlpha (c : HolChar) (h : isLowerChar c = true) : isAlphaChar c = true := by
  simp [isAlphaChar, h]

end Flapjack.CakeParser.FromSexp
