import Flapjack.Compiler.Backend.BvlInline.Proofs.TraversalTotal
import Aesop

/-! Total source-shaped BVL call inlining and executable correspondence. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

mutual
/-- Inline calls in one expression using the already-processed code tree. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_sing_def"]
def tickInlineSing {A : Type} (code : Spt (A × Exp)) : Exp → Exp
  | .var n => .var n
  | .ifThenElse a b c => .ifThenElse (tickInlineSing code a) (tickInlineSing code b) (tickInlineSing code c)
  | .let xs body => .let (tickInlineList code xs) (tickInlineSing code body)
  | .raise body => .raise (tickInlineSing code body)
  | .handle body handler => .handle (tickInlineSing code body) (tickInlineSing code handler)
  | .tick body => .tick (tickInlineSing code body)
  | .force location index => .force location index
  | .op op xs => .op op (tickInlineList code xs)
  | .call ticks dest xs =>
    match dest with
    | none => .call ticks none (tickInlineList code xs)
    | some name =>
      match sptLookup name code with
      | none => .call ticks (some name) (tickInlineList code xs)
      | some (_, body) => .let (tickInlineList code xs) (mkTick (ticks + 1) body)
termination_by expression => sizeOf expression

/-- Inline calls in each expression of a list. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_sing_def"]
def tickInlineList {A : Type} (code : Spt (A × Exp)) : List Exp → List Exp
  | [] => []
  | e :: es => tickInlineSing code e :: tickInlineList code es
termination_by expressions => sizeOf expressions
end

/-- List form of call inlining; the mutual traversal satisfies the original
list and singleton equations. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_def"]
def tickInline {A : Type} (code : Spt (A × Exp)) (expressions : List Exp) : List Exp :=
  tickInlineList code expressions

/-- The single-expression and list traversals agree with tick inlining. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_sing"]
theorem tickInlineSing_equivalence {A : Type} (code : Spt (A × Exp)) :
    (∀ expression, tickInline code [expression] = [tickInlineSing code expression]) ∧
      (∀ expressions, tickInlineList code expressions = tickInline code expressions) := by
  constructor
  · intro expression; simp [tickInline, tickInlineList]
  · intro expressions; rfl

/-- The list traversal is the map of the single-expression traversal; this
auxiliary decomposition has no standalone HOL declaration. -/
theorem tickInlineList_eq_map {A : Type} (code : Spt (A × Exp)) (expressions : List Exp) :
    tickInlineList code expressions = expressions.map (tickInlineSing code) := by
  induction expressions with
  | nil => simp [tickInlineList]
  | cons first rest ih => simp [tickInlineList, ih]

private theorem mapM_eq_map {α β : Type} (visit : α → Option β) (f : α → β)
    (correct : ∀ x y, visit x = some y → y = f x) (xs : List α) (ys : List β)
    (run : xs.mapM visit = some ys) : ys = xs.map f := by
  induction xs generalizing ys with
  | nil => simpa using run.symm
  | cons x rest ih =>
    simp only [List.mapM_cons] at run
    cases first : visit x with
    | none => simp [first] at run
    | some value =>
      cases remaining : rest.mapM visit with
      | none => simp [first, remaining] at run
      | some values =>
        simp [first, remaining] at run
        subst ys
        simp [correct x value first, ih values remaining]

/-- Any successful fuel-bounded run agrees with the total source traversal.
This executable correspondence has no standalone HOL declaration. -/
theorem inlineExpFuel_eq (fuel : Nat) (code : Spt (Nat × Exp)) (expression result : Exp)
    (run : inlineExpFuel fuel code expression = some result) : result = tickInlineSing code expression := by
  induction fuel generalizing expression result with
  | zero => simp [inlineExpFuel] at run
  | succ fuel ih =>
    cases expression <;> simp only [inlineExpFuel] at run <;>
      try simp only [tickInlineSing]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [tickInlineSing, tickInlineList_eq_map]
    all_goals aesop (add safe apply mapM_eq_map)

/-- The production bounded traversal always returns the total source result.
This executable correspondence has no standalone HOL declaration. -/
theorem inlineExpBounded_eq (fuel : Nat) (code : Spt (Nat × Exp)) (expression : Exp) :
    inlineExpBounded fuel code expression = some (tickInlineSing code expression) := by
  cases first : inlineExpFuel fuel code expression with
  | some result =>
    have correct := inlineExpFuel_eq fuel code expression result first
    simp [inlineExpBounded, first, correct]
  | none =>
    have bound : BvlToBvi.expBudget expression < max fuel (BvlToBvi.expBudget expression + 1) := by omega
    obtain ⟨result, run⟩ := inlineExpFuel_succeeds _ code expression bound
    have correct := inlineExpFuel_eq _ code expression result run
    simp [inlineExpBounded, first, run, correct]

end Flapjack.Compiler.Backend.BvlInline
