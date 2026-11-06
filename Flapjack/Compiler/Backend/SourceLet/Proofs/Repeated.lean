import Flapjack.Compiler.Backend.SourceLet.Proofs.Evaluate
import Flapjack.EvaluateProps.Declarations

/-! Repeated source let-lifting and declaration evaluation. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.EvaluateProps

/-- The direct recursive implementation has the same one-step view used in
the original definition. This is Flapjack proof infrastructure. -/
theorem liftLets_step_view (sofar : List Dec) (d : Dec) :
    liftLets sofar d = match liftLet d with
      | none => if sofar.isEmpty then none else some (sofar.reverse, d)
      | some (d1, d2) => liftLets (d1 :: sofar) d2 := by
  cases d with
  | dlet loc pat expr =>
    cases expr with
    | let_ name first body => cases name <;> simp [liftLets, liftLet]
    | _ => simp [liftLets, liftLet]
  | _ => simp [liftLets, liftLet]

private theorem liftLet_none_of_no_cases (d : Dec)
    (h1 : ∀ l p x y, d ≠ .dlet l p (.let_ none x y))
    (h2 : ∀ l p v x y, d ≠ .dlet l p (.let_ (some v) x y))
    (h3 : ∀ l p fs x, d ≠ .dlet l p (.letrec fs x)) : liftLet d = none := by
  cases d with
  | dlet loc pat expr =>
    cases expr with
    | let_ name first body =>
      cases name with
      | none => exact (h1 loc pat first body rfl).elim
      | some name => exact (h2 loc pat name first body rfl).elim
    | letrec funs body => exact (h3 loc pat funs body rfl).elim
    | _ => rfl
  | _ => rfl

/-- An error in a prefix also determines evaluation of a local declaration
whose private declarations extend that prefix. This is Flapjack proof
infrastructure with no separate HOL declaration. -/
theorem evaluateLocal_prefix_error {F : Type} (state next : State F) (env : SemEnv Value)
    (pre locals body : List Dec) (error : ErrorResult Value)
    (included : pre <+: locals) (run : evaluateDecs state env pre = (next, .err error)) :
    evaluateDecs state env [.dlocal locals body] = (next, .err error) := by
  obtain ⟨suffix, rfl⟩ := included
  rw [evaluateDecs_local, evaluateDecs_append, run]

/-- One recursive step of repeated let lifting. The induction hypothesis
is the same statement at the smaller declaration, and all evaluator results
are derived from the original source run. This Flapjack helper has no
separate HOL declaration. -/
theorem evaluateLiftLets_step {F : Type} (sofar : List Dec) (d d1 d2 : Dec)
    (state middle last : State F) (env inner : SemEnv Value)
    (result : Result (SemEnv Value) Value) (out : List Dec) (final : Dec)
    (accumulated : evaluateDecs state env sofar.reverse = (middle, .val inner))
    (source : evaluateDecs middle (extendDecEnv inner env) [d] = (last, result))
    (safe : result ≠ .err (.abort .typeError))
    (lifted : liftLet d = some (d1, d2))
    (rest : liftLets (d1 :: sofar) d2 = some (out, final))
    (ih : ∀ (state' middle' last' : State F) (env' inner' : SemEnv Value)
        (result' : Result (SemEnv Value) Value) (out' : List Dec) (final' : Dec),
      evaluateDecs state' env' (d1 :: sofar).reverse = (middle', .val inner') →
      evaluateDecs middle' (extendDecEnv inner' env') [d2] = (last', result') →
      result' ≠ .err (.abort .typeError) → liftLets (d1 :: sofar) d2 = some (out', final') →
      evaluateDecs state' env' [.dlocal out' [final']] = (last', result')) :
    evaluateDecs state env [.dlocal out [final]] = (last, result) := by
  have liftedRun := evaluate_lift_let middle last (extendDecEnv inner env) d d1 d2 result source safe lifted
  rw [evaluateDecs_local] at liftedRun
  cases first : evaluateDecs middle (extendDecEnv inner env) [d1] with
  | mk next firstResult =>
    cases firstResult with
    | err error =>
      have originalError : (next, .err error) = (last, result) := by simpa [first] using liftedRun
      have prefixError : evaluateDecs state env (sofar.reverse ++ [d1]) = (next, .err error) := by
        rw [evaluateDecs_append, accumulated]
        simp [first, combineDecResult]
      have included := liftLets_isPrefix (d1 :: sofar) d2 out final rest
      have included' : sofar.reverse ++ [d1] <+: out := by simpa only [List.reverse_cons] using included
      exact (evaluateLocal_prefix_error state next env (sofar.reverse ++ [d1]) out [final] error included' prefixError).trans originalError
    | val newEnv =>
      have remaining : evaluateDecs next (extendDecEnv newEnv (extendDecEnv inner env)) [d2] = (last, result) := by
        simpa [first] using liftedRun
      have nextAccumulated : evaluateDecs state env (d1 :: sofar).reverse =
          (next, .val (extendDecEnv newEnv inner)) := by
        rw [List.reverse_cons, evaluateDecs_append, accumulated]
        dsimp only
        rw [first]
        rfl
      apply ih state next last env (extendDecEnv newEnv inner) result out final nextAccumulated
      · simpa only [extendDecEnv_assoc] using remaining
      · exact safe
      · exact rest

/-- Repeated lifting preserves the declaration result after an already
evaluated prefix, provided the source run does not produce a type error. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "evaluate_lift_lets"]
theorem evaluate_lift_lets {F : Type} (sofar : List Dec) (d : Dec) :
    ∀ (state middle last : State F) (env inner : SemEnv Value)
      (result : Result (SemEnv Value) Value) (out : List Dec) (final : Dec),
      evaluateDecs state env sofar.reverse = (middle, .val inner) →
      evaluateDecs middle (extendDecEnv inner env) [d] = (last, result) →
      result ≠ .err (.abort .typeError) → liftLets sofar d = some (out, final) →
      evaluateDecs state env [.dlocal out [final]] = (last, result) := by
  induction sofar, d using liftLets.induct with
  | case1 sofar loc pat first body ih =>
    intro state middle last env inner result out final accumulated source safe lifted
    apply evaluateLiftLets_step sofar (.dlet loc pat (.let_ none first body))
      (.dlet loc .pany first) (.dlet loc pat body) state middle last env inner result out final
      accumulated source safe (by rfl)
    · simpa only [liftLets] using lifted
    · exact ih
  | case2 sofar loc pat name first body ih =>
    intro state middle last env inner result out final accumulated source safe lifted
    apply evaluateLiftLets_step sofar (.dlet loc pat (.let_ (some name) first body))
      (.dlet loc (.pvar name) first) (.dlet loc pat body) state middle last env inner result out final
      accumulated source safe (by rfl)
    · simpa only [liftLets] using lifted
    · exact ih
  | case3 sofar loc pat funs body ih =>
    intro state middle last env inner result out final accumulated source safe lifted
    apply evaluateLiftLets_step sofar (.dlet loc pat (.letrec funs body))
      (.dletrec loc funs) (.dlet loc pat body) state middle last env inner result out final
      accumulated source safe (by rfl)
    · simpa only [liftLets] using lifted
    · exact ih
  | case4 sofar d empty h1 h2 h3 =>
    intro state middle last env inner result out final accumulated source safe lifted
    have noStep := liftLet_none_of_no_cases d h1 h2 h3
    simp [liftLets_step_view, noStep, empty] at lifted
  | case5 sofar d nonempty h1 h2 h3 =>
    intro state middle last env inner result out final accumulated source safe lifted
    have noStep := liftLet_none_of_no_cases d h1 h2 h3
    simp only [liftLets_step_view, noStep, nonempty] at lifted
    obtain ⟨rfl, rfl⟩ := lifted
    rw [evaluateDecs_local, accumulated]
    simpa using source

end Flapjack.Compiler.Backend.SourceLet
