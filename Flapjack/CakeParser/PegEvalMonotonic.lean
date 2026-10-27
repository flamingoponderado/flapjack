import Flapjack.CakeParser.Frontend

/-! Stability of completed evaluations under additional parser fuel. This is
Flapjack infrastructure for reasoning about the bounded PEG interpreter. -/
namespace Flapjack.CakeParser.PegEval

/-- Once an evaluation completes, increasing its fuel by one does not change
its result. -/
theorem eval_more_one (fuel : Nat) (expr : PegSyntax.PegExpr) (input : List (Token × Misc.Location.Locs))
    (h : eval fuel expr input ≠ .exhausted) :
    eval (fuel + 1) expr input = eval fuel expr input := by
  induction fuel generalizing expr input with
  | zero => simp [eval] at h
  | succ fuel ih =>
    cases expr <;> (conv => lhs; try rw [eval]) <;> (conv => rhs; try rw [eval]) <;>
      (try rw [eval] at h) <;>
      repeat' (split at h <;> simp_all <;> try simp_all [ih])
    all_goals cases input <;> simp [eval]

/-- Any additional fuel preserves a completed PEG evaluation. -/
theorem eval_more (fuel extra : Nat) (expr : PegSyntax.PegExpr)
    (input : List (Token × Misc.Location.Locs))
    (h : eval fuel expr input ≠ .exhausted) :
    eval (fuel + extra) expr input = eval fuel expr input := by
  induction extra with
  | zero => simp
  | succ extra ih =>
    have completed : eval (fuel + extra) expr input ≠ .exhausted := by simpa [ih] using h
    rw [Nat.add_succ, eval_more_one (fuel + extra) expr input completed, ih]

/-- Once complete, top-level token parsing is stable under any additional PEG
fuel. This does not prove that a particular fuel bound suffices. -/
theorem parseTokensFuel_more (fuel extra : Nat) (tokens : List (Token × Misc.Location.Locs))
    (h : Frontend.parseTokensFuel fuel tokens ≠ .exhausted) :
    Frontend.parseTokensFuel (fuel + extra) tokens = Frontend.parseTokensFuel fuel tokens := by
  have completed : eval fuel (.nt (.inl .nTopLevelDecs) .id) tokens ≠ .exhausted := by
    intro he
    simp [Frontend.parseTokensFuel, he] at h
  simp only [Frontend.parseTokensFuel, eval_more fuel extra _ _ completed]

/-- Increasing PEG fuel preserves a completed source parse when lexer fuel is
held fixed. The lexer and AST conversion bounds are separate obligations. -/
theorem parseSourceFuel_more (lexerFuel parserFuel extra : Nat)
    (source : List Basis.Pure.MlString.HolChar)
    (h : Frontend.parseSourceFuel lexerFuel parserFuel source ≠ .exhausted) :
    Frontend.parseSourceFuel lexerFuel (parserFuel + extra) source =
      Frontend.parseSourceFuel lexerFuel parserFuel source := by
  cases hlex : Lexer.lexFuel lexerFuel source Misc.Location.defaultLoc with
  | none => simp [Frontend.parseSourceFuel, hlex] at h
  | some tokens =>
    simp only [Frontend.parseSourceFuel, hlex] at h ⊢
    exact parseTokensFuel_more parserFuel extra tokens h

end Flapjack.CakeParser.PegEval
