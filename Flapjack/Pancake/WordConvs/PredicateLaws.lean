module

public import Flapjack.Pancake.WordConvs
public import Flapjack.Pancake.WordLang
public import Flapjack.HolRef
public import Mathlib.Tactic.Tauto

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

/-- HOL `every_var_conj` (`wordConvsScript.sml`): the complete program
checker distributes over the conjunction of two predicates, including its
return-dependent traversal of Call handlers. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_conj"
  (words_as_type_indexed_bitvec)]
theorem everyVarConj {width : Nat} [NeZero width] (P : Nat → Bool)
    (prog : WordLangProgHOL (BitVec width)) (Q : Nat → Bool) :
    (everyVarHOL P prog && everyVarHOL Q prog) =
      everyVarHOL (fun x => P x && Q x) prog := by
  have listConj (values : List Nat) :
      (values.all P && values.all Q) = values.all (fun x => P x && Q x) := by
    induction values with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.all_cons]
      rw [← ih]
      simp [Bool.and_assoc, Bool.and_left_comm]
  have nameConj (names : WordLangCutsetsHOL) :
      (everyNameHOL P names && everyNameHOL Q names) =
        everyNameHOL (fun x => P x && Q x) names := by
    simp only [everyNameHOL]
    rw [← listConj ((sptToAList names.1).map Prod.fst),
      ← listConj ((sptToAList names.2).map Prod.fst)]
    simp [Bool.and_assoc, Bool.and_left_comm]
  have expConj (expression : WordLangExpHOL (BitVec width)) :
      (everyVarExpHOL P expression && everyVarExpHOL Q expression) =
        everyVarExpHOL (fun x => P x && Q x) expression :=
    everyVarExpConj P expression Q
  have instConj (instruction : WordLangInst (BitVec width)) :
      (everyVarInstHOL P instruction && everyVarInstHOL Q instruction) =
        everyVarInstHOL (fun x => P x && Q x) instruction :=
    everyVarInstConj P instruction Q
  have immConj (immediate : WordRegImm (BitVec width)) :
      (everyVarImmHOL P immediate && everyVarImmHOL Q immediate) =
        everyVarImmHOL (fun x => P x && Q x) immediate := by
    cases immediate with
    | imm value => simp [everyVarImmHOL]
    | reg name => simp [everyVarImmHOL]
  induction prog using everyVarHOL.induct
  case case13 returns target arguments handler ih =>
    cases returns with
    | none =>
      rw [Bool.eq_iff_iff]
      simp only [everyVarHOL, ← listConj arguments, Bool.and_eq_true]
      tauto
    | some returns =>
      rcases returns with ⟨values, names, body, label, entry⟩
      cases handler with
      | none =>
        obtain ⟨ihReturns, -⟩ := ih
        rw [Bool.eq_iff_iff] at ihReturns
        simp only [Bool.and_eq_true] at ihReturns
        rw [Bool.eq_iff_iff]
        simp only [everyVarHOL, ← listConj arguments, ← listConj values,
          ← nameConj names, Bool.and_eq_true]
        tauto
      | some handler =>
        rcases handler with ⟨value, body, label, entry⟩
        obtain ⟨ihReturns, ihHandler⟩ := ih
        dsimp only at ihHandler
        rw [Bool.eq_iff_iff] at ihReturns ihHandler
        simp only [Bool.and_eq_true] at ihReturns ihHandler
        rw [Bool.eq_iff_iff]
        simp only [everyVarHOL, ← listConj arguments, ← listConj values,
          ← nameConj names, Bool.and_eq_true]
        tauto
  all_goals
    rw [Bool.eq_iff_iff] at *
    simp only [Bool.and_eq_true] at *
    simp only [everyVarHOL, ← listConj, ← nameConj, ← expConj, ← instConj, ← immConj,
      Bool.and_eq_true]
    try tauto

end Flapjack.Pancake.WordConvs
