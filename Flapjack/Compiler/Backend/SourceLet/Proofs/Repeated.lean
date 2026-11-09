module

public import Flapjack.Compiler.Backend.SourceLet.Proofs.Evaluate
public import Flapjack.EvaluateProps.Declarations

@[expose] public section

/-! Repeated source let-lifting and declaration evaluation. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL Flapjack.EvaluateProps

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
    (ih : ∀ (state' : State F) (env' : SemEnv Value) (middle' : State F) (inner' : SemEnv Value)
        (last' : State F)
        (result' : Result (SemEnv Value) Value) (out' : List Dec) (final' : Dec),
      evaluateDecs state' env' (d1 :: sofar).reverse = (middle', .val inner') ∧
      evaluateDecs middle' (extendDecEnv inner' env') [d2] = (last', result') ∧
      result' ≠ .err (.abort .typeError) ∧ liftLets (d1 :: sofar) d2 = some (out', final') →
      evaluateDecs state' env' [.dlocal out' [final']] = (last', result')) :
    evaluateDecs state env [.dlocal out [final]] = (last, result) := by
  have liftedRun := evaluate_lift_let middle (extendDecEnv inner env) d last result d1 d2 ⟨source, safe, lifted⟩
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
      apply ih state env next (extendDecEnv newEnv inner) last result out final
      exact ⟨nextAccumulated, by simpa only [extendDecEnv_assoc] using remaining, safe, rest⟩

/-- Repeated lifting preserves the declaration result after an already
evaluated prefix, provided the source run does not produce a type error. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "evaluate_lift_lets"]
theorem evaluate_lift_lets {F : Type} (sofar : List Dec) (d : Dec) :
    ∀ (state : State F) (env : SemEnv Value) (middle : State F) (inner : SemEnv Value) (last : State F)
      (result : Result (SemEnv Value) Value) (out : List Dec) (final : Dec),
      evaluateDecs state env sofar.reverse = (middle, .val inner) ∧
      evaluateDecs middle (extendDecEnv inner env) [d] = (last, result) ∧
      result ≠ .err (.abort .typeError) ∧ liftLets sofar d = some (out, final) →
      evaluateDecs state env [.dlocal out [final]] = (last, result) := by
  induction sofar, d using liftLets.induct with
  | case1 sofar d d1 d2 step ih =>
    rintro state env middle inner last result out final ⟨accumulated, source, safe, lifted⟩
    apply evaluateLiftLets_step sofar d d1 d2 state middle last env inner result out final
      accumulated source safe step
    · rw [liftLets.eq_def, step] at lifted
      exact lifted
    · exact ih
  | case2 sofar d noStep empty =>
    rintro state env middle inner last result out final ⟨accumulated, source, safe, lifted⟩
    rw [liftLets.eq_def, noStep] at lifted
    simp [empty] at lifted
  | case3 sofar d noStep nonempty =>
    rintro state env middle inner last result out final ⟨accumulated, source, safe, lifted⟩
    rw [liftLets.eq_def, noStep] at lifted
    simp only [nonempty] at lifted
    obtain ⟨rfl, rfl⟩ := lifted
    rw [evaluateDecs_local, accumulated]
    simpa using source

end Flapjack.Compiler.Backend.SourceLet
