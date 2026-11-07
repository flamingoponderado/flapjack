import Flapjack.Compiler.Backend.BvlToBvi.Proofs.EvaluateOk

/-! The complete clocked BVL evaluation well-formedness invariant. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value State expsWeight expWeight)
open Flapjack.SemanticPrimitivesHOL (Result)

namespace EvaluateAllCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvaluateAllCarrier

/-- Clock-and-expression-size induction for the evaluator invariant. -/
theorem evaluateOk_bounded {C F : Type} (clock : Nat) :
    ∀ expressions, @evalOk C F clock expressions := by
  induction clock using Nat.strongRecOn with
  | ind clock clockIH =>
    have below : @evalOkBelow C F clock := by
      intro expressions env s t result smaller run ok envOk
      exact clockIH s.clock smaller expressions env s t result (Nat.le_refl _) run ok envOk
    have rank : ∀ weight : Nat, ∀ expressions : List Bvl.Exp,
        expsWeight expressions = weight → @evalOk C F clock expressions := by
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have smaller : ∀ expressions : List Bvl.Exp, expsWeight expressions < weight →
            @evalOk C F clock expressions := by
          intro expressions lt
          exact weightIH (expsWeight expressions) lt expressions rfl
        intro expressions measure
        cases expressions with
        | nil => exact evaluateOk_nil clock
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluateOk_cons clock first second tail
            · apply smaller; simp only [expsWeight] at measure ⊢; omega
            · apply smaller; simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var index => exact evaluateOk_var clock index
            | ifThenElse condition yes no =>
              apply evaluateOk_if clock condition yes no
              all_goals apply smaller
              all_goals simp only [expsWeight, expWeight] at measure ⊢
              all_goals omega
            | «let» bindings body =>
              apply evaluateOk_let clock bindings body
              all_goals apply smaller
              all_goals simp only [expsWeight, expWeight] at measure ⊢
              all_goals omega
            | raise body =>
              apply evaluateOk_raise clock body
              apply smaller; simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle body handler =>
              apply evaluateOk_handle clock body handler
              all_goals apply smaller
              all_goals simp only [expsWeight, expWeight] at measure ⊢
              all_goals omega
            | tick body =>
              apply evaluateOk_tick clock body
              apply smaller; simp only [expsWeight, expWeight] at measure ⊢; omega
            | op op args =>
              apply evaluateOk_op clock op args
              apply smaller; simp only [expsWeight, expWeight] at measure ⊢; omega
            | call ticks dest args =>
              intro env s t result clockLe run ok envOk
              have argsIH := smaller args (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              have bodyIH : @evalOkBelow C F s.clock := by
                intro expressions env' s' t' result' lt run' ok' envOk'
                exact below expressions env' s' t' result' (by omega) run' ok' envOk'
              exact evaluateOk_call clock ticks dest args env s argsIH bodyIH t result clockLe run ok envOk
            | force location index =>
              intro env s t result clockLe run ok envOk
              have bodyIH : @evalOkBelow C F s.clock := by
                intro expressions env' s' t' result' lt run' ok' envOk'
                exact below expressions env' s' t' result' (by omega) run' ok' envOk'
              exact evaluateOk_force location index env s bodyIH t result run ok envOk
    intro expressions
    exact rank (expsWeight expressions) expressions rfl

/-- Evaluation preserves source-state and result well-formedness, as well as
the original environment, for both normal results and exceptions. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "evaluate_ok"
  (fmap_as_finite_support := [refs])]
theorem evaluateOk {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) (result : Result (List Value) Value)
    (t : Flapjack.Compiler.Backend.BvlSem.State C F)
    (run : BvlSem.evaluateTuple (expressions, env, s) = (result, t))
    (ok : stateOk s) (envOk : bvOkList s.refs env) :
    stateOk t ∧
      (match result with
       | .val values => bvOkList t.refs values
       | .err (.raise value) => bvOk t.refs value
       | .err (.abort _) => True) ∧
      bvOkList t.refs env := by
  have preserved := evaluateOk_bounded s.clock expressions env s t result (Nat.le_refl _) run ok envOk
  cases result with
  | val values => simpa [evalResultOk] using preserved
  | err error =>
    cases error <;> simpa [evalResultOk] using preserved

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
