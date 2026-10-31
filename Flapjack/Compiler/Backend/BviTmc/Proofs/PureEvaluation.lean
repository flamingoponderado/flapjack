import Flapjack.Compiler.Backend.BviTmc.Proofs.VariableEvaluation

/-! Evaluation of the expressions accepted by TMC's purity test. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi BviSem BvlSem
namespace PureEvaluation

mutual
/-- A pure singleton has a state-independent value; this strengthens the
source list theorem for use in extraction proofs. -/
theorem evaluatePureExp {C F : Type} (e : Bvi.Exp) (n : Nat)
    (pure : pureExp n e = true) (env : List Value) (bound : n ≤ env.length) :
    ∃ value, ∀ state : BviState C F, evaluate [e] env state = (.val [value], state) := by
  cases e with
  | var index =>
    have indexBound : index < env.length := by simp [pureExp] at pure; omega
    refine ⟨env[index], ?_⟩
    intro state
    simp [BviSem.evaluate, indexBound]
  | «let» args body =>
    have parts : pureExp n body = true ∧ pureExps n args = true := by simpa [pureExp] using pure
    obtain ⟨values, valuesRun⟩ := evaluatePureExps (C := C) (F := F) args n parts.2 env bound
    obtain ⟨value, valueRun⟩ := evaluatePureExp (C := C) (F := F) body n parts.1 (values ++ env) (by simp; omega)
    refine ⟨value, ?_⟩
    intro state
    simp [BviSem.evaluate, valuesRun, valueRun, BviSem.fixClock]
  | op op args =>
    have parts : pureOp op args = true ∧ pureExps n args = true := by simpa [pureExp] using pure
    cases op with
    | intOp intOp =>
      cases intOp with
      | const number =>
        cases args with
        | nil =>
          have small : BackendCommon.smallEnoughInt number := by
            simpa [pureOp, BackendCommon.smallEnoughInt] using parts.1
          refine ⟨.number number, ?_⟩
          intro state
          simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
            BviSem.doAppAux, small]
        | cons arg args => simp [pureOp] at parts
      | _ => simp [pureOp] at parts
    | blockOp block =>
      cases block with
      | cons tag =>
        obtain ⟨values, valuesRun⟩ := evaluatePureExps (C := C) (F := F) args n parts.2 env bound
        refine ⟨.block tag values.reverse, ?_⟩
        intro state
        simp [BviSem.evaluate, valuesRun, BviSem.fixClock, BviTailrec.doApp_blockCons]
      | _ => simp [pureOp] at parts
    | _ => simp [pureOp] at parts
  | _ => simp [pureExp] at pure
termination_by expBudget e
decreasing_by all_goals simp_all [expBudget] <;> omega

private theorem evaluatePureExps {C F : Type} (xs : List Bvi.Exp) (n : Nat)
    (pure : pureExps n xs = true) (env : List Value) (bound : n ≤ env.length) :
    ∃ values, ∀ state : BviState C F, evaluate xs env state = (.val values, state) := by
  cases xs with
  | nil => exact ⟨[], fun state => by simp [BviSem.evaluate]⟩
  | cons x xs =>
    have parts : pureExp n x = true ∧ pureExps n xs = true := by simpa [pureExps] using pure
    obtain ⟨value, headRun⟩ := evaluatePureExp (C := C) (F := F) x n parts.1 env bound
    obtain ⟨values, tailRun⟩ := evaluatePureExps (C := C) (F := F) xs n parts.2 env bound
    refine ⟨value :: values, ?_⟩
    intro state
    change evaluateTuple (x :: xs, env, state) = _
    rw [evaluateCons]
    simp [BviSem.evaluateTuple, headRun, tailRun, Flapjack.holHd]
termination_by listBudget xs
decreasing_by all_goals simp_all [listBudget]; omega
end

/-- The mutual pure-expression and pure-list evaluation lemma. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_pure_exp_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluate_pure_exp_lemma {C F : Type} :
    (∀ (e : Bvi.Exp) n, pureExp n e = true → ∀ env, n ≤ env.length →
      ∃ values, ∀ state : BviState C F, evaluate [e] env state = (.val values, state)) ∧
    (∀ (_ : Option Bvi.Exp), True) ∧
    (∀ (xs : List Bvi.Exp) n, pureExps n xs = true → ∀ env, n ≤ env.length →
      ∃ values, ∀ state : BviState C F, evaluate xs env state = (.val values, state)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e n pure env bound
    obtain ⟨value, run⟩ := evaluatePureExp (C := C) (F := F) e n pure env bound
    exact ⟨[value], run⟩
  · intro _; trivial
  · intro xs n pure env bound
    exact evaluatePureExps xs n pure env bound

/-- Pure expression lists evaluate successfully to state-independent values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_pure_exps"
  (fmap_as_finite_support := [refs])]
theorem evaluate_pure_exps {C F : Type} (n : Nat) (xs : List Bvi.Exp)
    (pure : pureExps n xs = true) (env : List Value) (bound : n ≤ env.length) :
    ∃ values, ∀ state : BviState C F, evaluate xs env state = (.val values, state) :=
  evaluatePureExps xs n pure env bound

theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

end PureEvaluation
end Flapjack.Compiler.Backend.BviTmc
