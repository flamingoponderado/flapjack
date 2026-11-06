import Flapjack.Compiler.Backend.DbVars

/-! Lookup properties of the handler compiler's variable sets. -/
namespace Flapjack.Compiler.Backend.DbVars

/-- Looking up a variable in the accumulated sparse tree gives the inserted
unit when it is visible at the current offset, and otherwise preserves the
previous lookup. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "lookup_db_to_set_acc"]
theorem lookupDbToSetAcc (d : DbVarSet) (n k : Nat) (s : NumSet) :
    sptLookup n (dbToSetAcc k d s) =
      if hasVar (n + k) d then some () else sptLookup n s := by
  induction d generalizing n k s with
  | empty => simp [dbToSetAcc, hasVar]
  | var v =>
      by_cases h : v < k
      · have hn : n + k ≠ v := by omega
        simp [dbToSetAcc, hasVar, h, hn]
      · by_cases heq : n + k = v
        · have hk : v - k = n := by omega
          simp [dbToSetAcc, hasVar, h, heq, hk, sptLookup_sptInsert_same]
        · have hk : n ≠ v - k := by omega
          simp [dbToSetAcc, hasVar, h, heq, sptLookup_sptInsert_ne _ _ _ _ hk]
  | shift offset d ih =>
      simpa [dbToSetAcc, hasVar, Nat.add_assoc] using ih n (k + offset) s
  | union a b iha ihb =>
      simp only [dbToSetAcc, hasVar, iha, ihb, Bool.or_eq_true]
      split <;> simp_all

/-- A variable is live exactly when its materialized tree contains it. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "lookup_db_to_set"]
theorem lookupDbToSet (n : Nat) (d : DbVarSet) :
    (hasVar n d = true) ↔ sptLookup n (dbToSet d) = some () := by
  rw [dbToSet, lookupDbToSetAcc]
  simp

/-- Enumerating the tree preserves exactly its live indices. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "MEM_vars_to_list"]
theorem memVarsToList (n : Nat) (d : DbVarSet) :
    (n ∈ varsToList d) ↔ hasVar n d = true := by
  rw [lookupDbToSet]
  have h := sptLookup_sptFromAList_sptToAList n (dbToSet d)
  rw [sptLookup_sptFromAList] at h
  constructor
  · intro hm
    obtain ⟨⟨key, value⟩, hp, hk⟩ := List.mem_map.mp hm
    simp only at hk
    subst key
    cases value
    have hl := sptAListLookup_eq_of_mem_unique n () _ hp (by
      intro other _
      cases other
      rfl)
    exact h ▸ hl
  · intro hl
    have hm := sptAListLookup_mem n (sptToAList (dbToSet d)) () (h.trans hl)
    exact List.mem_map.mpr ⟨(n, ()), hm, rfl⟩

/-- A left fold of variable unions records the list's members and the
accumulator's existing members. -/
theorem hasVarFoldUnion (vs : List Nat) (n : Nat) (s : DbVarSet) :
    (hasVar n (vs.foldl (fun a v => .union (.var v) a) s) = true) ↔
      n ∈ vs ∨ hasVar n s = true := by
  induction vs generalizing s with
  | nil => simp
  | cons v vs ih => simp [List.foldl, ih, hasVar, or_assoc, or_left_comm]

/-- Building a variable set from a list preserves membership. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "MEM_vars_from_list"]
theorem memVarsFromList (vs : List Nat) (n : Nat) :
    (hasVar n (varsFromList vs) = true) ↔ n ∈ vs := by
  simpa [varsFromList, hasVar] using hasVarFoldUnion vs n .empty

/-- Flattening variable-set expressions preserves live-variable membership. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "has_var_vars_flatten"]
theorem hasVarVarsFlatten (n : Nat) (d : DbVarSet) :
    hasVar n (varsFlatten d) = hasVar n d := by
  apply Bool.eq_iff_iff.mpr
  exact (memVarsFromList _ _).trans (memVarsToList _ _)

end Flapjack.Compiler.Backend.DbVars
