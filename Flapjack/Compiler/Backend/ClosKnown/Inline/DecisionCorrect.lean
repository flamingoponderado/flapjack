import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineDecrease
import Flapjack.Compiler.Backend.ClosKnown.Inline.Free.Correct

/-! Source decision and agreement with the former checked implementation. -/
namespace Flapjack.Compiler.Backend.ClosKnown

/-- The previous checked decision, retained for the all-input equivalence
proof. It is Flapjack infrastructure rather than a separate HOL definition. -/
private def previousDecision (fuel : Nat) (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) : Option InliningDecision := do
  if loc.isSome then return .nothing
  match approx with
  | .closNoInline target n => pure (if arity == n then .annotate target else .nothing)
  | .clos target n body size =>
      if arity != n then return .nothing
      if size < c.inlineFactor * (1 + arity) then
        if !(← containsClosuresBounded fuel body) then
          if ← ClosCall.closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body) then
            return .letInline body
      pure (.annotate target)
  | _ => pure .nothing

/-- The source decision produces the same result as the previous checked
decision for every configuration, approximation, location, and fuel. -/
theorem decideInlineFuel_eq_previous (fuel : Nat) (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) :
    decideInlineFuel fuel c approx loc arity = previousDecision fuel c approx loc arity := by
  cases loc with
  | some loc => cases approx <;> simp [decideInlineFuel, decideInlineHOL, previousDecision]
  | none =>
    cases approx with
    | clos target n body size =>
      have closed := closedFuel_correct fuel
        (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body)
      simp only [decideInlineFuel, decideInlineHOL, previousDecision, Option.isSome_none,
        containsClosuresBounded, Bind.bind, Option.bind, Pure.pure, closed]
      split <;> simp_all
      all_goals (repeat' split) <;> simp_all
    | _ => simp [decideInlineFuel, decideInlineHOL, previousDecision]

/-- An inlining decision containing a body requires a positive factor. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "decide_inline_LetInline"]
theorem decideInlineLetInline {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineHOL c approx loc arity = .letInline body) : 0 < c.inlineFactor := by
  by_cases zero : c.inlineFactor = 0
  · cases loc <;> cases approx <;> simp [decideInlineHOL, zero] at h <;>
      split at h <;> simp_all
  · omega

end Flapjack.Compiler.Backend.ClosKnown
