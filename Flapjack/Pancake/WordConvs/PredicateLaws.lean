module

public import Flapjack.Pancake.WordConvs
public import Flapjack.Pancake.WordLang
public import Flapjack.HolRef

@[expose] public section

/-! Conjunction laws for the `wordConvsScript.sml` predicate checkers
(`every_var_inst_conj`, `every_var_exp_conj`, `every_var_conj`). HOL's
checkers are `bool`-valued over `num -> bool` predicates, so the source's
`/\\` and `<=>` render as `&&` and Boolean equality. -/

namespace Flapjack.Pancake.WordConvs

open Flapjack

/-- HOL `every_var_inst_conj` (`wordConvsScript.sml`): the instruction checker
distributes over the conjunction of two predicates. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_inst_conj"
  (words_as_type_indexed_bitvec)]
theorem everyVarInstConj {width : Nat} [NeZero width] (P : Nat → Bool)
    (instruction : WordLangInst (BitVec width)) (Q : Nat → Bool) :
    (everyVarInstHOL P instruction && everyVarInstHOL Q instruction) =
      everyVarInstHOL (fun x => P x && Q x) instruction := by
  simp only [everyVarInstHOL]
  repeat' split
  all_goals simp [everyVarImmHOL, Bool.and_left_comm, Bool.and_comm]
  all_goals split
  all_goals simp [Bool.and_left_comm, Bool.and_comm]

/-- HOL `every_var_exp_conj` (`wordConvsScript.sml`): the expression checker
distributes over the conjunction of two predicates. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_exp_conj"
  (words_as_type_indexed_bitvec)]
theorem everyVarExpConj {width : Nat} [NeZero width] (P : Nat → Bool)
    (expression : WordLangExpHOL (BitVec width)) (Q : Nat → Bool) :
    (everyVarExpHOL P expression && everyVarExpHOL Q expression) =
      everyVarExpHOL (fun x => P x && Q x) expression := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      (everyVarExpHOL P e && everyVarExpHOL Q e) = everyVarExpHOL (fun x => P x && Q x) e)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      (everyVarExpsHOL P es && everyVarExpsHOL Q es) =
        everyVarExpsHOL (fun x => P x && Q x) es)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value
    simp [everyVarExpHOL]
  · intro name
    simp [everyVarExpHOL]
  · intro store
    simp [everyVarExpHOL]
  · intro address ih
    simpa [everyVarExpHOL] using ih
  · intro operator arguments ih
    simpa [everyVarExpHOL] using ih
  · intro operator left right ihLeft ihRight
    simp only [everyVarExpHOL]
    rw [← ihLeft, ← ihRight]
    simp [Bool.and_assoc, Bool.and_left_comm]
  · simp [everyVarExpsHOL]
  · intro head tail ihHead ihTail
    simp only [everyVarExpsHOL]
    rw [← ihHead, ← ihTail]
    simp [Bool.and_assoc, Bool.and_left_comm]

end Flapjack.Pancake.WordConvs
