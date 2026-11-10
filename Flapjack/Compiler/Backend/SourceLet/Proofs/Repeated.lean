module

public import Flapjack.Compiler.Backend.SourceLet.Proofs.Evaluate
public import Flapjack.EvaluateProps.Declarations

@[expose] public section

/-! Repeated source let-lifting and declaration evaluation. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL Flapjack.EvaluateProps

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
    rintro state env middle inner last result out final ⟨accumulated, source, safe, rest⟩
    rw [liftLets.eq_def, step] at rest
    have liftedRun := evaluate_lift_let middle (extendDecEnv inner env) d last result d1 d2 ⟨source, safe, step⟩
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
        obtain ⟨suffix, rfl⟩ := included'
        rw [evaluateDecs_local, evaluateDecs_append, prefixError]
        exact originalError
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
