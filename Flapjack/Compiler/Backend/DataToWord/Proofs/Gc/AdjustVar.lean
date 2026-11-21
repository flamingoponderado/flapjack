module

public import Flapjack.Compiler.Backend.DataToWord.Variables

@[expose] public section

/-! Bounds on variable numbering used by the garbage-collector proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Adjusted data-variable slots cannot be the reserved slot 15. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_not_15", simp]
theorem adjustVar_ne_fifteen (a2 : Nat) : adjustVar a2 ≠ 15 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_DIV_2` (`data_to_word_gcProofScript.sml:309-313`); the
HOL free variable `n` is universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_DIV_2"]
theorem adjust_var_DIV_2 {n : Nat} : (adjustVar n - 2) / 2 = n := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_DIV_2_ANY` (`data_to_word_gcProofScript.sml:315-319`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_DIV_2_ANY"]
theorem adjust_var_DIV_2_ANY {n : Nat} : adjustVar n / 2 = n + 1 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `EVEN_adjust_var` (`data_to_word_gcProofScript.sml:321-326`);
HOL `EVEN k` is `k % 2 = 0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "EVEN_adjust_var"]
theorem EVEN_adjust_var {n : Nat} : adjustVar n % 2 = 0 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_eq_numeral` (`data_to_word_gcProofScript.sml:328-340`).
HOL `NUMERAL` is the identity on `num`, so `NUMERAL k` is the natural number
`k`, universally quantified like the HOL free variables. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_eq_numeral"]
theorem adjust_var_eq_numeral {n k : Nat} :
    adjustVar n = k ↔ k % 2 = 0 ∧ k ≠ 0 ∧ n = (k - 2) / 2 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_NEQ_0` (`data_to_word_gcProofScript.sml:342-346`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_NEQ_0"]
theorem adjust_var_NEQ_0 {n : Nat} : adjustVar n ≠ 0 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_NEQ_1` (`data_to_word_gcProofScript.sml:348-352`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_NEQ_1"]
theorem adjust_var_NEQ_1 {n : Nat} : adjustVar n ≠ 1 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_NEQ` (`data_to_word_gcProofScript.sml:354-365`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_NEQ"]
theorem adjust_var_NEQ {n : Nat} :
    adjustVar n ≠ 0 ∧ adjustVar n ≠ 1 ∧ adjustVar n ≠ 3 ∧ adjustVar n ≠ 5 ∧
      adjustVar n ≠ 7 ∧ adjustVar n ≠ 9 ∧ adjustVar n ≠ 11 ∧ adjustVar n ≠ 13 := by
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_11` (`data_to_word_gcProofScript.sml:373-377`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_11"]
theorem adjust_var_11 {n m : Nat} : adjustVar n = adjustVar m ↔ n = m := by
  simp only [adjustVar]
  omega

/-- Exact HOL `IMP_adjust_var` (`data_to_word_gcProofScript.sml:504-510`);
HOL `EVEN n` is `n % 2 = 0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "IMP_adjust_var"]
theorem IMP_adjust_var {n : Nat} : n ≠ 0 ∧ n % 2 = 0 → adjustVar ((n - 2) / 2) = n := by
  intro h
  simp only [adjustVar]
  omega

/-- Exact HOL `adjust_var_NOT_0` (`data_to_word_gcProofScript.sml:4688-4692`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_NOT_0"]
theorem adjust_var_NOT_0 {n : Nat} : adjustVar n ≠ 0 := adjust_var_NEQ_0

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
