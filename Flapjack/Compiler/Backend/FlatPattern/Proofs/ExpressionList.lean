import Flapjack.Compiler.Backend.FlatPattern.Proofs.ExpressionCases

/-! Ordered expression-list simulation for the flat pattern compiler. The
underlying evaluator and value/state relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Compiling an expression list maps each expression in order. -/
theorem compileExps_rows (cfg : Config) (expressions : List FlatLang.Exp) :
    (compileExps cfg expressions).2.2 = expressions.map (fun expression => (compileExp cfg expression).2.2) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
    cases first : compileExp cfg expression with
    | mk bound part =>
      cases part with
      | mk flag compiled =>
        cases tail : compileExps cfg rest with
        | mk tailBound part =>
          cases part with
          | mk tailFlag compiledTail => simpa [compileExps, first, tail] using ih

/-- List compilation bounds the head and tail compiler measures. -/
theorem compileExps_cons_bounds (cfg : Config) (first : FlatLang.Exp) (rest : List FlatLang.Exp) :
    (compileExp cfg first).1 ≤ (compileExps cfg (first :: rest)).1 ∧
      (compileExps cfg rest).1 ≤ (compileExps cfg (first :: rest)).1 := by
  cases head : compileExp cfg first with
  | mk bound part =>
    cases part with
    | mk flag compiled =>
      cases tail : compileExps cfg rest with
      | mk tailBound part =>
        cases part with
        | mk tailFlag compiledTail => simp [compileExps, head, tail]

/-- An error in the first expression stops a nonempty expression list. -/
theorem evaluate_list_first_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (firstRun : FlatSem.evaluate env state [first] = (next, .err error)) :
    FlatSem.evaluate env state (first :: second :: rest) =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, firstRun, FlatSem.fixClock]

/-- A successful first expression followed by an error propagates the error. -/
theorem evaluate_list_tail_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next final : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (value : FlatSem.Value) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (firstRun : FlatSem.evaluate env state [first] = (next, .val [value]))
    (tailRun : FlatSem.evaluate env { next with clock := min state.clock next.clock } (second :: rest) = (final, .err error)) :
    FlatSem.evaluate env state (first :: second :: rest) = (final, .err error) := by
  simp [FlatSem.evaluate, firstRun, FlatSem.fixClock, tailRun]

/-- Successful nonempty expression lists preserve the first result and tail order. -/
theorem evaluate_list_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next final : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (value : FlatSem.Value) (values : List FlatSem.Value)
    (firstRun : FlatSem.evaluate env state [first] = (next, .val [value]))
    (tailRun : FlatSem.evaluate env { next with clock := min state.clock next.clock } (second :: rest) = (final, .val values)) :
    FlatSem.evaluate env state (first :: second :: rest) = (final, .val (value :: values)) := by
  simp [FlatSem.evaluate, firstRun, FlatSem.fixClock, tailRun]

/-- The compilation bound for a list is below a positive limit exactly when
all its members have bounds below that limit. -/
theorem compileExps_bound_iff (cfg : Config) (expressions : List FlatLang.Exp) (n : Nat) (positive : 0 < n) :
    (compileExps cfg expressions).1 < n ↔ ∀ expression ∈ expressions, (compileExp cfg expression).1 < n := by
  induction expressions with
  | nil => simp [compileExps, positive]
  | cons first rest ih =>
    cases head : compileExp cfg first with
    | mk headBound part =>
      cases part with
      | mk headFlag headBody =>
        cases tail : compileExps cfg rest with
        | mk tailBound part =>
          cases part with
          | mk tailFlag tailBody =>
            simp only [compileExps, head, tail, List.mem_cons, forall_eq_or_imp] at ih ⊢
            constructor
            · intro bound
              exact ⟨by omega, ih.mp (by omega)⟩
            · intro ⟨firstBound, restBound⟩
              have tailBoundLt := ih.mpr restBound
              omega

/-- Reversing an expression list does not change whether its compilation bound
is below a positive limit. -/
theorem compileExps_reverse_bound (cfg : Config) (expressions : List FlatLang.Exp) (n : Nat)
    (bound : (compileExps cfg expressions).1 < n) : (compileExps cfg expressions.reverse).1 < n := by
  have positive : 0 < n := by omega
  apply (compileExps_bound_iff cfg expressions.reverse n positive).2
  intro expression member
  exact (compileExps_bound_iff cfg expressions n positive).1 bound expression (by simpa using member)

/-- Constructor evaluation wraps a successful argument list in one value. -/
theorem evaluate_con_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (run : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.con trace tag args] = (next, .val [.conv tag values.reverse]) := by
  simp [FlatSem.evaluate, run]

/-- Constructor evaluation propagates argument errors unchanged. -/
theorem evaluate_con_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state args.reverse = (next, .err error)) :
    FlatSem.evaluate env state [.con trace tag args] = (next, .err error) := by
  simp [FlatSem.evaluate, run]

end Flapjack.Compiler.Backend.FlatPattern
