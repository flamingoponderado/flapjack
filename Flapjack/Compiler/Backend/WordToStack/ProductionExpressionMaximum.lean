import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec
import Flapjack.Pancake.WordLang.MaxVarExp

namespace Flapjack

/-- Flapjack-only fold correspondence. Production scans from an accumulator;
the reviewed HOL maximum scans a list from zero. This auxiliary lemma has no
separate HOL original. -/
private theorem foldMaximum {α : Type} (value : α → Nat) (items : List α)
    (initial : Nat) :
    items.foldl (fun result item => max result (value item)) initial =
      max initial (maxList (items.map value)) := by
  induction items generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, maxList, ih, Nat.max_assoc]

/-- The actual production expression maximum equals the reviewed native
maximum after the existing total constructor codec, for every expression.
This is Flapjack-only correspondence between two Lean carriers, rather than
a port of a HOL theorem. No conversion-success or maximum-equality premise
is required. The Word-to-Stack frame and executed route remain separate. -/
theorem wordExpCakeMaxVar_eq_maxVarExpHOL {width : Nat} [NeZero width]
    (expression : WordExp (BitVec width)) :
    wordExpCakeMaxVar expression = maxVarExpHOL (wordExpToHOL expression) := by
  refine WordExp.rec
    (motive_1 := fun expression =>
      wordExpCakeMaxVar expression = maxVarExpHOL (wordExpToHOL expression))
    (motive_2 := fun expressions =>
      expressions.map wordExpCakeMaxVar =
        (expressions.map wordExpToHOL).map maxVarExpHOL)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value
    simp only [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL]
  · intro name
    simp only [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL]
  · intro store
    simp only [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL]
  · intro address ih
    simpa only [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL] using ih
  · intro operator arguments ih
    simp only [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL,
      foldMaximum, Nat.zero_max, ih]
  · intro operator left right ihLeft ihRight
    simp only [wordExpCakeMaxVar, wordExpToHOL, maxVarExpHOL, ihLeft, ihRight]
  · rfl
  · intro head tail ihHead ihTail
    simp only [List.map_cons, ihHead, ihTail]

/-- Complete production argument-list scan correspondence, including empty
lists and arbitrary initial maxima. Flapjack-only carrier infrastructure;
this is not a theorem about successful compilation or evaluation. -/
theorem wordExpCakeMaxVar_fold_eq_maxVarExpHOL {width : Nat} [NeZero width]
    (expressions : List (WordExp (BitVec width))) (initial : Nat) :
    expressions.foldl (fun result expression => max result (wordExpCakeMaxVar expression))
        initial =
      max initial (maxList ((expressions.map wordExpToHOL).map maxVarExpHOL)) := by
  rw [foldMaximum]
  congr 1
  simp only [List.map_map]
  apply congrArg maxList
  apply List.map_congr_left
  intro expression _
  exact wordExpCakeMaxVar_eq_maxVarExpHOL expression

end Flapjack
