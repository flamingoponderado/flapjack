import Flapjack.Compiler.Backend.BviTailrec.Proofs.HasRecTotal
import Flapjack.Compiler.Backend.BviTailrec.Rewrite

/-! Source-shaped recursion detection and its production correspondence. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

mutual
/-- Source recursion detection in the positions considered by the optimizer. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "has_rec_sing_def"]
def hasRecSing (loc : Nat) : Exp → Bool
  | .ifThenElse _ yes no => if hasRecSing loc yes then true else hasRecSing loc no
  | .let _ body | .tick body => hasRecSing loc body
  | .op _ args => if args.any (isRec loc) then true else hasRecList loc args
  | _ => false
termination_by e => sizeOf e

/-- Source left-to-right recursion detection over an expression list. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "has_rec_sing_def"]
def hasRecList (loc : Nat) : List Exp → Bool
  | [] => false
  | first :: rest => if hasRecSing loc first then true else hasRecList loc rest
termination_by es => sizeOf es
end

private theorem listBudget_pos (expressions : List Exp) : 0 < listBudget expressions := by
  cases expressions <;> simp [listBudget] <;> omega

/-- Original list-shaped recursion analysis, before the source's singleton
and list factoring. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "has_rec_def"]
def hasRec (loc : Nat) : List Exp → Bool
  | [] => false
  | first :: second :: rest => if hasRec loc [first] then true else hasRec loc (second :: rest)
  | [.ifThenElse _ yes no] => if hasRec loc [yes] then true else hasRec loc [no]
  | [.let _ body] | [.tick body] => hasRec loc [body]
  | [.op _ args] => if args.any (isRec loc) then true else hasRec loc args
  | [_] => false
termination_by expressions => listBudget expressions
decreasing_by
  all_goals simp_all only [listBudget, expBudget]
  all_goals try (have := listBudget_pos rest)
  all_goals omega

/-- The original single-expression recursion query. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "has_rec1_def"]
def hasRec1 (loc : Nat) (expression : Exp) : Bool := hasRec loc [expression]

mutual
/-- Singleton agreement between the original and factored source tests. -/
theorem hasRec_sing_eq (loc : Nat) (expression : Exp) :
    hasRec loc [expression] = hasRecSing loc expression := by
  cases expression with
  | ifThenElse condition yes no =>
    simp only [hasRec, hasRecSing, hasRec_sing_eq loc yes, hasRec_sing_eq loc no]
  | «let» bindings body => simpa only [hasRec, hasRecSing] using hasRec_sing_eq loc body
  | tick body => simpa only [hasRec, hasRecSing] using hasRec_sing_eq loc body
  | op op args => simp only [hasRec, hasRecSing, hasRec_list_eq loc args]
  | _ => simp [hasRec, hasRecSing]
termination_by sizeOf expression

/-- List agreement between the original and factored source tests. -/
theorem hasRec_list_eq (loc : Nat) (expressions : List Exp) :
    hasRec loc expressions = hasRecList loc expressions := by
  cases expressions with
  | nil => simp [hasRec, hasRecList]
  | cons first rest =>
    cases rest with
    | nil => simpa [hasRecList] using hasRec_sing_eq loc first
    | cons second tail =>
      simp only [hasRec, hasRecList, hasRec_sing_eq loc first, hasRec_list_eq loc (second :: tail)]
termination_by sizeOf expressions
end

/-- The original list recursion detector agrees with both factored tests. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "has_rec_eq"]
theorem hasRec_eq :
    (∀ e loc, hasRec loc [e] = hasRecSing loc e) ∧
      (∀ es loc, hasRec loc es = hasRecList loc es) :=
  ⟨fun e loc => hasRec_sing_eq loc e, fun es loc => hasRec_list_eq loc es⟩

/-- The list traversal recognizes exactly the disjunction of its members. -/
theorem hasRecList_eq_any (loc : Nat) (expressions : List Exp) :
    hasRecList loc expressions = expressions.any (hasRecSing loc) := by
  induction expressions with
  | nil => simp [hasRecList]
  | cons first rest ih => simp [hasRecList, ih, List.any_cons]

/-- A successful short-circuiting monadic fold agrees with a pure disjunction
when each successfully visited element agrees with its pure test. -/
private theorem foldRec_eq {α : Type} (xs : List α) (f : α → Option Bool) (g : α → Bool)
    (init result : Bool)
    (sound : ∀ x ∈ xs, ∀ b, f x = some b → b = g x)
    (run : xs.foldlM (fun found x => if found then pure true else f x) init = some result) :
    result = (init || xs.any g) := by
  induction xs generalizing init result with
  | nil => simpa using run.symm
  | cons first rest ih =>
    have tailSound : ∀ x ∈ rest, ∀ b, f x = some b → b = g x := by
      intro x member b found
      exact sound x (by simp [member]) b found
    cases init with
    | true =>
      have tail := ih true result tailSound (by simpa using run)
      simpa using tail
    | false =>
      cases firstRun : f first with
      | none => simp [firstRun] at run
      | some firstResult =>
        have firstEq := sound first (by simp) firstResult firstRun
        have tail := ih firstResult result tailSound (by simpa [firstRun] using run)
        simpa [firstEq, List.any_cons] using tail

/-- Any successful bounded recursion test returns the source-shaped result. -/
theorem hasRecFuel_eq (fuel loc : Nat) (expression : Exp) (result : Bool)
    (run : hasRecFuel fuel loc expression = some result) : result = hasRecSing loc expression := by
  induction fuel generalizing expression result with
  | zero => simp [hasRecFuel] at run
  | succ fuel ih =>
    cases expression with
    | ifThenElse condition yes no =>
      cases first : hasRecFuel fuel loc yes with
      | none => simp [hasRecFuel, first] at run
      | some value =>
        have valueEq := ih yes value first
        cases value with
        | true => simpa [hasRecFuel, first, hasRecSing, ← valueEq] using run.symm
        | false =>
          have noRun : hasRecFuel fuel loc no = some result := by simpa [hasRecFuel, first] using run
          have noEq := ih no result noRun
          simpa [hasRecSing, ← valueEq] using noEq
    | «let» bindings body =>
      simpa [hasRecSing] using ih body result (by simpa [hasRecFuel] using run)
    | tick body =>
      simpa [hasRecSing] using ih body result (by simpa [hasRecFuel] using run)
    | op op args =>
      by_cases direct : args.any (isRec loc) = true
      · simpa [hasRecFuel, hasRecSing, direct] using run.symm
      · have directFalse : args.any (isRec loc) = false := by cases h : args.any (isRec loc) <;> simp_all
        have foldRun : args.foldlM (fun found x => if found then pure true else hasRecFuel fuel loc x) false =
            some result := by simpa [hasRecFuel, directFalse] using run
        have folded := foldRec_eq args (hasRecFuel fuel loc) (hasRecSing loc) false result
          (by intro x _ b found; exact ih x b found) foldRun
        simpa [hasRecSing, directFalse, hasRecList_eq_any] using folded
    | _ => simpa [hasRecFuel, hasRecSing] using run.symm

/-- Retrying with a structural budget always returns the same recursion
decision as the source definition, independently of the initial fuel. -/
theorem hasRecBounded_eq (fuel loc : Nat) (expression : Exp) :
    hasRecBounded fuel loc expression = some (hasRecSing loc expression) := by
  obtain ⟨result, run⟩ := hasRecBounded_succeeds fuel loc expression
  have same : result = hasRecSing loc expression := by
    cases first : hasRecFuel fuel loc expression with
    | some initial =>
      have initialEq : initial = result := by simpa [hasRecBounded, first] using run
      subst result
      exact hasRecFuel_eq fuel loc expression initial first
    | none =>
      have retry : hasRecFuel (max fuel (expBudget expression + 1)) loc expression = some result := by
        simpa [hasRecBounded, first] using run
      exact hasRecFuel_eq _ loc expression result retry
  simpa [same] using run

/-- The executed recursion query agrees with the original CakeML query for
every expression and every initial traversal budget. -/
theorem hasRecBounded_eq_hasRec1 (fuel loc : Nat) (expression : Exp) :
    hasRecBounded fuel loc expression = some (hasRec1 loc expression) := by
  rw [hasRecBounded_eq, hasRec1, hasRec_sing_eq]

/-- The candidate check rejects expressions for which CakeML's recursion
query returns false. -/
theorem checkExpFuel_noRec (fuel loc arity : Nat) (expression : Exp)
    (noRec : hasRec1 loc expression = false) :
    checkExpFuel fuel loc arity expression = some none := by
  simp [checkExpFuel, hasRecBounded_eq_hasRec1, noRec]

/-- Retrying cannot introduce a rewrite when the source recursion query
rejects the expression. -/
theorem compileExpBounded_noRec (fuel loc next arity : Nat) (expression : Exp)
    (noRec : hasRec1 loc expression = false) :
    compileExpBounded fuel loc next arity expression = some none := by
  simp [compileExpBounded, compileExpFuel, checkExpFuel_noRec fuel loc arity expression noRec]

/-- Processing a program with no recursive candidates preserves every
entry and the next-label counter. -/
theorem compileEachFuel_noRec (fuel next : Nat) (program : List (Nat × Nat × Exp))
    (noRec : ∀ entry ∈ program, hasRec1 entry.1 entry.2.2 = false) :
    compileEachFuel fuel next program = some (next, program) := by
  induction program generalizing next with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    have head := noRec (loc, arity, body) (by simp)
    have tail : ∀ entry ∈ rest, hasRec1 entry.1 entry.2.2 = false := by
      intro entry member
      exact noRec entry (by simp [member])
    simp [compileEachFuel, compileExpBounded_noRec fuel loc next arity body head, ih next tail]

/-- The production tail-recursion pass leaves every no-candidate program
unchanged, whether the pass is enabled or disabled. -/
theorem compileProgFuel_noRec (fuel : Nat) (enabled : Bool) (next : Nat)
    (program : List (Nat × Nat × Exp))
    (noRec : ∀ entry ∈ program, hasRec1 entry.1 entry.2.2 = false) :
    compileProgFuel fuel enabled next program = some (next, program) := by
  cases enabled with
  | false => rfl
  | true => simpa [compileProgFuel] using compileEachFuel_noRec fuel next program noRec

end Flapjack.Compiler.Backend.BviTailrec
