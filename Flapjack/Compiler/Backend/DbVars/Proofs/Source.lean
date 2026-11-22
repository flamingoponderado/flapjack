module

public import Flapjack.Compiler.Backend.DbVars
public import Flapjack.Compiler.Backend.DbVars.Proofs.Lookup
public import Flapjack.Misc.Sptree.ToAList

@[expose] public section

/-! Source lemmas about variable-set construction and materialization. -/
namespace Flapjack.Compiler.Backend.DbVars

/-- The optimized union has an empty identity on both sides. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "mk_Union_Empty"]
theorem mk_Union_Empty (A : DbVarSet) : mkUnion .empty A = A ∧ mkUnion A .empty = A := by
  constructor
  · rfl
  · cases A
    all_goals rfl

/-- Folding pairs into a list and a union is the same as unzipping first and
unioning the second components before the accumulator. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "FOLDR_mk_Union_UNZIP"]
theorem FOLDR_mk_Union_UNZIP {α : Type} (A : DbVarSet) (l : List (α × DbVarSet)) :
    List.foldr (fun (x, vars) (ts, frees) => (x :: ts, mkUnion vars frees)) ([], A) l =
      (let (ts, fvs) := l.unzip
       (ts, listMkUnion (fvs ++ [A]))) := by
  induction l with
  | nil => simp [listMkUnion, (mk_Union_Empty A).2]
  | cons pair rest ih =>
    obtain ⟨x, vars⟩ := pair
    simp [listMkUnion, ih]

/-- Accumulating variables preserves sparse-tree well-formedness. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "wf_db_to_set_acc"]
theorem wf_db_to_set_acc (s : DbVarSet) (n : Nat) (a : NumSet)
    (hwf : sptWf a = true) : sptWf (dbToSetAcc n s a) = true := by
  revert n a hwf
  induction s with
  | empty =>
    intro n a hwf
    simpa [dbToSetAcc] using hwf
  | var v =>
    intro n a hwf
    by_cases h : v < n
    · simp [dbToSetAcc, h, hwf]
    · simp only [dbToSetAcc, h, if_false]
      exact sptWfInsert (v - n) () a hwf
  | shift k d ih =>
    intro n a hwf
    simpa [dbToSetAcc] using ih (n + k) a hwf
  | union x y ihx ihy =>
    intro n a hwf
    simp only [dbToSetAcc]
    exact ihx n (dbToSetAcc n y a) (ihy n a hwf)

/-- Materialized variable sets are well formed. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "wf_db_to_set"]
theorem wf_db_to_set (db : DbVarSet) : sptWf (dbToSet db) = true := by
  rw [dbToSet]
  exact wf_db_to_set_acc db 0 .ln rfl

/-- A variable occurs in a union of a list exactly when it occurs in a member. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "has_var_list_mk_Union"]
theorem has_var_list_mk_Union (ls : List DbVarSet) (n : Nat) :
    hasVar n (listMkUnion ls) = ls.any (hasVar n) := by
  induction ls with
  | nil => simp [listMkUnion, hasVar]
  | cons x xs ih =>
    simp only [listMkUnion, List.any_cons]
    rw [hasVar_mkUnion, ih]

/-- Shifting a variable set shifts the sparse-tree lookup. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "lookup_db_to_set_Shift"]
theorem lookup_db_to_set_Shift (n k : Nat) (s : DbVarSet) :
    sptLookup n (dbToSet (.shift k s)) = sptLookup (n + k) (dbToSet s) := by
  simp [dbToSet, dbToSetAcc, lookupDbToSetAcc]

/-- A fold of variable unions records the list's members and the
accumulator's existing members. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "has_var_FOLDL_Union"]
theorem has_var_FOLDL_Union (vs : List Nat) (n : Nat) (s : DbVarSet) :
    (hasVar n (vs.foldl (fun acc v => .union (.var v) acc) s) = true) ↔
      n ∈ vs ∨ hasVar n s = true :=
  hasVarFoldUnion vs n s

/-- The enumeration of a variable set has no duplicates. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "ALL_DISTINCT_vars_to_list"]
theorem ALL_DISTINCT_vars_to_list (d : DbVarSet) : (varsToList d).Nodup :=
  sptAllDistinctMapFstToAList (dbToSet d)

end Flapjack.Compiler.Backend.DbVars
