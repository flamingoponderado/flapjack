import Flapjack.Pancake.PanLang.Prog

namespace Flapjack.Pancake.PanLang

open Flapjack.Basis.Pure.MlString

private theorem map_filter_ne_of_injective {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → β) (hinj : Function.Injective f)
    (values : List α) (name : α) :
    (values.filter (fun candidate => candidate != name)).map f =
      (values.map f).filter (fun candidate => candidate != f name) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    by_cases hhead : head = name
    · subst head
      simp [ih]
    · have hmapped : f head != f name := by
        have hne : ¬ f head = f name := fun heq => hhead (hinj heq)
        simp [hne]
      simp [hhead, hmapped, ih]

/-- Flapjack-specific projection lemma for the exact HOL
    `free_var_ids_def` port above.  HOL has no separate theorem stating how
    its `MlS` names decode into production `String` names; this proves that
    clause-by-clause projection for every exact program.  It is useful when a
    production compiler branch computes a fresh name from `freeVarIds` while
    the exact compiler computes it from `freeVarIdsHOL`. -/
@[simp] theorem freeVarIdsHOL_map_toStringOfBytes {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    (freeVarIdsHOL program).map toStringOfBytes =
      Flapjack.freeVarIds (progOfHOL program) := by
  have hname_injective : Function.Injective toStringOfBytes := by
    intro left right heq
    have hrange := congrArg ofString heq
    simpa only [ofString_toStringOfBytes] using hrange
  have hvarList (expressions : List (ExpHOL width))
      (hvars : ∀ expression ∈ expressions,
        (varExpHOL expression).map toStringOfBytes =
          Flapjack.expLocalVars (expOfHOL expression)) :
      ((expressions.map varExpHOL).flatten).map toStringOfBytes =
        Flapjack.expLocalVars.expLocalVarsList (expressions.map expOfHOL) := by
    induction expressions with
    | nil => simp [Flapjack.expLocalVars.expLocalVarsList]
    | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        Flapjack.expLocalVars.expLocalVarsList.eq_2]
      rw [hvars head (by simp), ih (fun expression hmem => hvars expression (by simp [hmem]))]
  have hvarFieldList (fields : List (MlS × ExpHOL width))
      (hvars : ∀ field ∈ fields,
        (varExpHOL field.2).map toStringOfBytes =
          Flapjack.expLocalVars (expOfHOL field.2)) :
      ((fields.map (fun field => varExpHOL field.2)).flatten).map toStringOfBytes =
        Flapjack.expLocalVars.expLocalVarsFieldList
          (fields.map (fun field => (toStringOfBytes field.1, expOfHOL field.2))) := by
    induction fields with
    | nil => simp [Flapjack.expLocalVars.expLocalVarsFieldList]
    | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        Flapjack.expLocalVars.expLocalVarsFieldList.eq_2]
      rw [hvars head (by simp), ih (fun field hmem => hvars field (by simp [hmem]))]
  have hexp (expression : ExpHOL width) :
      (varExpHOL expression).map toStringOfBytes =
        Flapjack.expLocalVars (expOfHOL expression) := by
    fun_induction varExpHOL expression <;>
      simp_all [Flapjack.expLocalVars, expOfHOL, List.map_append]
    all_goals first
      | apply hvarList _ <;> assumption
      | apply hvarFieldList _ <;> assumption
  have hargs (arguments : List (ExpHOL width)) :
      ((arguments.map varExpHOL).flatten).map toStringOfBytes =
        (arguments.map expOfHOL).flatMap Flapjack.expLocalVars := by
    induction arguments with
    | nil => rfl
    | cons head tail ih =>
      simp [hexp head, ih, List.flatMap]
  fun_induction freeVarIdsHOL program <;>
    simp_all [Flapjack.freeVarIds, progOfHOL,
      map_filter_ne_of_injective, List.map_append, List.map_cons, List.map_nil,
      List.flatMap]
  all_goals cases ‹VarKind› <;> simp_all

/-- On the parser-supported byte-ranged subset, the exact HOL
    `free_var_ids_def` result encoded from production syntax decodes to the
    production `freeVarIds` list.  The premise is required only for the
    `progOfHOL (progToHOL program)` round trip; the general exact-carrier
    projection above is premise-free.  This is Flapjack-specific codec
    infrastructure, not a separate HOL theorem. -/
theorem freeVarIdsHOL_progToHOL_byteRanged {width : Nat} [NeZero width]
    (program : Prog (BitVec width)) (hprogram : ProgByteRanged program) :
    (freeVarIdsHOL (progToHOL program)).map toStringOfBytes =
      Flapjack.freeVarIds program := by
  rw [freeVarIdsHOL_map_toStringOfBytes, progOfHOL_progToHOL program hprogram]

end Flapjack.Pancake.PanLang
