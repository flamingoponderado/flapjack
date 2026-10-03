import Flapjack.Pancake.WordLang.MaxVarExp

namespace Flapjack.WordConvs

/-- Flapjack induction infrastructure: a natural maximum selects one of its
arguments, so an arbitrary predicate holding on both holds on the maximum.
This is not a separate HOL declaration port. -/
private theorem predicateMax (P : Nat → Bool) (a b : Nat)
    (ha : P a = true) (hb : P b = true) : P (max a b) = true := by
  rcases Nat.le_total a b with h | h
  · simpa [Nat.max_eq_right h] using hb
  · simpa [Nat.max_eq_left h] using ha

/-- Original generic expression maximum introduction. The zero premise covers
constant and lookup expressions and empty operator argument lists. The mutual
list motive follows the same expression traversal, without a numeric bound
or a restriction on the predicate. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "max_var_exp_IMP" (words_as_type_indexed_bitvec)]
theorem maxVarExpImp {width : Nat} [NeZero width]
    (P : Nat → Bool) (expression : WordLangExpHOL (BitVec width))
    (hyp : P 0 = true ∧ everyVarExpHOL P expression = true) :
    P (maxVarExpHOL expression) = true := by
  have result : ∀ e : WordLangExpHOL (BitVec width),
      P 0 = true → everyVarExpHOL P e = true → P (maxVarExpHOL e) = true := by
    refine WordLangExpHOL.rec
      (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
        P 0 = true → everyVarExpHOL P e = true → P (maxVarExpHOL e) = true)
      (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
        P 0 = true → everyVarExpsHOL P es = true →
          P (maxList (es.map maxVarExpHOL)) = true)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro value hzero _; simpa [maxVarExpHOL] using hzero
    · intro name _ h; simpa [maxVarExpHOL, everyVarExpHOL] using h
    · intro store hzero _; simpa [maxVarExpHOL] using hzero
    · intro address ih hzero h
      simpa only [maxVarExpHOL] using ih hzero (by simpa [everyVarExpHOL] using h)
    · intro operator arguments ih hzero h
      simpa only [maxVarExpHOL] using ih hzero (by simpa [everyVarExpHOL] using h)
    · intro operator left right ihLeft ihRight hzero h
      simp only [everyVarExpHOL, Bool.and_eq_true] at h
      simpa only [maxVarExpHOL] using predicateMax P _ _ (ihLeft hzero h.1) (ihRight hzero h.2)
    · intro hzero _; simpa [maxList] using hzero
    · intro head tail ihHead ihTail hzero h
      simp only [everyVarExpsHOL, Bool.and_eq_true] at h
      exact predicateMax P _ _ (ihHead hzero h.1) (ihTail hzero h.2)
  exact result expression hyp.1 hyp.2

end Flapjack.WordConvs
