import Flapjack.CakeParser.PegEval

/-! Input-consumption invariant for the bounded PEG interpreter. This is
Flapjack infrastructure, not a port of the relational HOL PEG theorem. -/
namespace Flapjack.CakeParser.PegEval

/-- A successful evaluation leaves a suffix of its original input. -/
theorem eval_suffix (fuel : Nat) (expr : PegSyntax.PegExpr)
    (input rest : List (Token × Misc.Location.Locs)) (trees : List ParseTree)
    (h : eval fuel expr input = .success trees rest) : rest <:+ input := by
  induction fuel generalizing expr input rest trees with
  | zero => simp [eval] at h
  | succ fuel ih =>
    cases expr <;> simp only [eval] at h <;> try simp_all
    all_goals repeat' (split at h <;> try simp_all)
    all_goals first
      | exact ih _ _ _ _ (by assumption)
      | (rename_i _ _ _ firstEq _ _ _ secondEq
         exact (ih _ _ _ _ secondEq).trans (ih _ _ _ _ firstEq))

/-- A successful evaluation never increases the number of remaining tokens. -/
theorem eval_remaining_length_le (fuel : Nat) (expr : PegSyntax.PegExpr)
    (input rest : List (Token × Misc.Location.Locs)) (trees : List ParseTree)
    (h : eval fuel expr input = .success trees rest) : rest.length ≤ input.length :=
  (eval_suffix fuel expr input rest trees h).length_le

/-- If a successful evaluation leaves the original number of tokens, it left
the input unchanged. -/
theorem eval_remaining_eq_of_length (fuel : Nat) (expr : PegSyntax.PegExpr)
    (input rest : List (Token × Misc.Location.Locs)) (trees : List ParseTree)
    (h : eval fuel expr input = .success trees rest) (sameLength : rest.length = input.length) :
    rest = input :=
  (eval_suffix fuel expr input rest trees h).eq_of_length_le (Nat.le_of_eq sameLength.symm)

end Flapjack.CakeParser.PegEval
