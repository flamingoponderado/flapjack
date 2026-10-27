import Flapjack.CakeParser.PegEvalMonotonic
import Aesop

/-! An unbounded, error-erased relation for the first-order PEG interpreter.
This is Flapjack infrastructure: unlike HOL's `peg_eval`, it uses the
specialized CakeML grammar and does not retain failure locations or diagnostic
stacks. Correspondence with the original relational semantics remains open. -/
namespace Flapjack.CakeParser.PegRelation
open Flapjack.Misc.Location PegActions PegChecks PegSyntax PegGrammar PegEval

abbrev Input := List (Token × Locs)

/-- Fuel-free evaluation rules for the executable first-order CakeML PEG. -/
inductive Evaluates : PegExpr → Input → Result → Prop where
  | empty (values input) : Evaluates (.empty values) input (.success values input)
  | anySuccess (m x xs) : Evaluates (.any m) (x :: xs) (.success (evalTokenMap m x) xs)
  | anyFailure (m) : Evaluates (.any m) [] .failure
  | tokenSuccess (check m x xs) (h : evalToken check x = true) :
      Evaluates (.token check m) (x :: xs) (.success (evalTokenMap m x) xs)
  | tokenFailure (check m x xs) (h : evalToken check x = false) :
      Evaluates (.token check m) (x :: xs) .failure
  | tokenEof (check m) : Evaluates (.token check m) [] .failure
  | ntFailure (rule action input expr) (h : ntRule rule = some expr)
      (he : Evaluates expr input .failure) : Evaluates (.nt rule action) input .failure
  | ntSuccess (rule action input expr trees rest) (h : ntRule rule = some expr)
      (he : Evaluates expr input (.success trees rest)) :
      Evaluates (.nt rule action) input (.success (evalUnary action trees) rest)
  | seqFailureLeft (a b action input) (ha : Evaluates a input .failure) :
      Evaluates (.seq a b action) input .failure
  | seqFailureRight (a b action input left middle) (ha : Evaluates a input (.success left middle))
      (hb : Evaluates b middle .failure) : Evaluates (.seq a b action) input .failure
  | seqSuccess (a b action input left middle right rest)
      (ha : Evaluates a input (.success left middle)) (hb : Evaluates b middle (.success right rest)) :
      Evaluates (.seq a b action) input (.success (evalBinary action left right) rest)
  | choiceFailure (a b input) (ha : Evaluates a input .failure) (hb : Evaluates b input .failure) :
      Evaluates (.choice a b) input .failure
  | choiceRight (a b input trees rest) (ha : Evaluates a input .failure)
      (hb : Evaluates b input (.success trees rest)) :
      Evaluates (.choice a b) input (.success trees rest)
  | choiceLeft (a b input trees rest) (ha : Evaluates a input (.success trees rest)) :
      Evaluates (.choice a b) input (.success trees rest)
  | repeatDone (e input) (h : Evaluates e input .failure) :
      Evaluates (.repeat e) input (.success [] input)
  | repeatSuccess (e input left middle right rest) (ha : Evaluates e input (.success left middle))
      (hb : Evaluates (.repeat e) middle (.success right rest)) :
      Evaluates (.repeat e) input (.success (left ++ right) rest)
  | repeatFailure (e input left middle) (ha : Evaluates e input (.success left middle))
      (hb : Evaluates (.repeat e) middle .failure) : Evaluates (.repeat e) input .failure
  | notSuccess (e values input) (h : Evaluates e input .failure) :
      Evaluates (.not e values) input (.success values input)
  | notFailure (e values input trees rest) (h : Evaluates e input (.success trees rest)) :
      Evaluates (.not e values) input .failure
  | error (message input) : Evaluates (.error message) input .failure

/-- Every completed bounded run has a derivation in the fuel-free relation. -/
theorem eval_sound (fuel : Nat) (expr : PegExpr) (input : Input) (result : Result)
    (finished : result ≠ .exhausted) (h : eval fuel expr input = result) :
    Evaluates expr input result := by
  induction fuel generalizing expr input result with
  | zero => simp [eval] at h; subst result; contradiction
  | succ fuel ih =>
    cases result <;> simp_all
    all_goals cases expr <;> simp only [eval] at h <;> try simp_all
    all_goals repeat' (split at h <;> try simp_all)
    all_goals try rcases h with ⟨rfl, rfl⟩
    all_goals try (apply Evaluates.notFailure; apply ih <;> first | assumption | simp)
    all_goals aesop (add unsafe constructors Evaluates)

/-- The fuel-free relation only describes completed results. -/
theorem evaluates_completed {expr : PegExpr} {input : Input} {result : Result}
    (h : Evaluates expr input result) : result ≠ .exhausted := by
  cases h <;> simp

private theorem commonFuel {e₁ e₂ : PegExpr} {s₁ s₂ : Input} {r₁ r₂ : Result}
    (h₁ : ∃ n, eval n e₁ s₁ = r₁) (h₂ : ∃ n, eval n e₂ s₂ = r₂)
    (ne₁ : r₁ ≠ .exhausted) (ne₂ : r₂ ≠ .exhausted) :
    ∃ n, eval n e₁ s₁ = r₁ ∧ eval n e₂ s₂ = r₂ := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  have first := eval_more n m e₁ s₁ (by simpa [hn] using ne₁)
  have second := eval_more m n e₂ s₂ (by simpa [hm] using ne₂)
  exact ⟨n + m, by simpa [hn] using first, by simpa [hm, Nat.add_comm] using second⟩

/-- A derivation can be reproduced by the bounded interpreter at some fuel. -/
theorem eval_complete {expr : PegExpr} {input : Input} {result : Result}
    (h : Evaluates expr input result) : ∃ fuel, eval fuel expr input = result := by
  induction h
  all_goals try (solve | refine ⟨1, ?_⟩; simp [eval, *])
  all_goals try (solve | rename_i ih; obtain ⟨n, hn⟩ := ih; refine ⟨n + 1, ?_⟩; simp [eval, *])
  all_goals rename_i ih₁ ih₂
  all_goals obtain ⟨n, hn₁, hn₂⟩ := commonFuel ih₁ ih₂ (by simp) (by simp)
  all_goals refine ⟨n + 1, ?_⟩
  all_goals simp [eval, *]

/-- The fuel-free relation describes exactly the completed bounded runs. -/
theorem evaluates_iff {expr : PegExpr} {input : Input} {result : Result} :
    Evaluates expr input result ↔ ∃ fuel, eval fuel expr input = result ∧ result ≠ .exhausted := by
  constructor
  · intro h
    obtain ⟨fuel, hfuel⟩ := eval_complete h
    exact ⟨fuel, hfuel, evaluates_completed h⟩
  · rintro ⟨fuel, hfuel, completed⟩
    exact eval_sound fuel expr input result completed hfuel

/-- The fuel-free relation has at most one result for an expression and input. -/
theorem evaluates_deterministic {expr : PegExpr} {input : Input} {first second : Result}
    (h₁ : Evaluates expr input first) (h₂ : Evaluates expr input second) : first = second := by
  obtain ⟨_, hfirst, hsecond⟩ := commonFuel (eval_complete h₁) (eval_complete h₂)
    (evaluates_completed h₁) (evaluates_completed h₂)
  exact hfirst.symm.trans hsecond

end Flapjack.CakeParser.PegRelation
