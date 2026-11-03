import Flapjack.Compiler.Backend.ClosOp.Proofs.DontLiftEvaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend

/-! Cases of the source expression-lifting evaluation theorem. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace LiftEvaluatePort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end LiftEvaluatePort

/-- The quantified conclusion of `lift_exps_thm`, used to express its
functional induction hypotheses. This is Flapjack proof infrastructure. -/
def LiftEvaluate {C F : Type} (xs : List ClosLang.Exp) (n : Nat) (binds : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (s0 : State C F) (ys : List ClosLang.Exp) (k : Nat)
    (vs0 : List Value) (binds2 : List ClosLang.Exp) (s1 s2 : State C F)
    (res0 : Result (List Value) Value),
    evaluate binds env s0 = (.val vs0, s1) ∧
    evaluate xs env s1 = (res0, s2) ∧ n = binds.length ∧
    liftExpsHOL xs n binds = (ys, k, binds2) →
    ∃ res, evaluate binds2 env s0 = (res, s2) ∧
      (∀ err, res = .err err → res0 = res) ∧
      ∀ (ws : List Value) (s3 : State C F) (bindVals : List Value),
        res = .val bindVals → ∃ vs, res0 = .val vs ∧
          evaluate ys (bindVals ++ ws) s3 = (.val vs, s3)

/-- Empty-list case of the original functional induction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_thm"
  (fmap_as_finite_support := [refs, code])]
theorem liftExpsThmNil {C F : Type} (n : Nat) (binds : List ClosLang.Exp) :
    ∀ (env : List Value) (s0 : State C F) (ys : List ClosLang.Exp) (k : Nat)
      (vs0 : List Value) (binds2 : List ClosLang.Exp) (s1 s2 : State C F)
      (res0 : Result (List Value) Value),
      evaluate binds env s0 = (.val vs0, s1) ∧ evaluate [] env s1 = (res0, s2) ∧
      n = binds.length ∧ liftExpsHOL [] n binds = (ys, k, binds2) →
      ∃ res, evaluate binds2 env s0 = (res, s2) ∧
        (∀ err, res = .err err → res0 = res) ∧
        ∀ (ws : List Value) (s3 : State C F) (bindVals : List Value),
          res = .val bindVals → ∃ vs, res0 = .val vs ∧
            evaluate ys (bindVals ++ ws) s3 = (.val vs, s3) := by
  intro env s0 ys k vs0 binds2 s1 s2 res0 ⟨bindRun, run, _, lifted⟩
  simp only [liftExpsHOL, Prod.mk.injEq] at lifted
  rcases lifted with ⟨rfl, _, rfl⟩
  simp only [evaluate, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨.val vs0, bindRun, by simp, by intro ws s3 bindVals h; exact ⟨[], rfl, by simp [evaluate]⟩⟩

/-- Literal case of the original functional induction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_thm"
  (fmap_as_finite_support := [refs, code])]
theorem liftExpsThmDontLift {C F : Type} (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (n : Nat) (binds : List ClosLang.Exp) (literal : dontLift x = true)
    (ih : @LiftEvaluate C F xs n binds) :
    ∀ (env : List Value) (s0 : State C F) (ys : List ClosLang.Exp) (k : Nat)
      (vs0 : List Value) (binds2 : List ClosLang.Exp) (s1 s2 : State C F)
      (res0 : Result (List Value) Value),
      evaluate binds env s0 = (.val vs0, s1) ∧ evaluate (x :: xs) env s1 = (res0, s2) ∧
      n = binds.length ∧ liftExpsHOL (x :: xs) n binds = (ys, k, binds2) →
      ∃ res, evaluate binds2 env s0 = (res, s2) ∧
        (∀ err, res = .err err → res0 = res) ∧
        ∀ (ws : List Value) (s3 : State C F) (bindVals : List Value),
          res = .val bindVals → ∃ vs, res0 = .val vs ∧
            evaluate ys (bindVals ++ ws) s3 = (.val vs, s3) := by
  intro env s0 ys k vs0 binds2 s1 s2 res0 ⟨bindRun, run, nEq, lifted⟩
  cases tailLift : liftExpsHOL xs n binds with
  | mk tailYs tailPair =>
    cases tailPair with
    | mk tailK tailBinds =>
      simp only [liftExpsHOL, literal, ↓reduceIte, tailLift,
        Prod.mk.injEq] at lifted
      rcases lifted with ⟨rfl, rfl, rfl⟩
      cases headRun : evaluate [x] env s1 with
      | mk headResult headState =>
        obtain ⟨v, valueEq, stateEq⟩ := dontRval x env s1 headState headResult ⟨literal, headRun⟩
        subst headResult
        subst headState
        rw [ClosProps.evaluate_cons_value x xs env s1 s1 v headRun] at run
        cases tailRun : evaluate xs env s1 with
        | mk tailResult tailState =>
          cases tailResult with
          | err err =>
            simp only [tailRun] at run
            cases run
            obtain ⟨res, bindsRun, errEq, values⟩ :=
              ih env s0 tailYs tailK vs0 tailBinds s1 s2 (.err err)
                ⟨bindRun, tailRun, nEq, tailLift⟩
            refine ⟨res, bindsRun, errEq, ?_⟩
            intro ws s3 bindVals resEq
            obtain ⟨vs, impossible, _⟩ := values ws s3 bindVals resEq
            cases impossible
          | val tailValues =>
            simp only [tailRun] at run
            cases run
            obtain ⟨res, bindsRun, errEq, values⟩ :=
              ih env s0 tailYs tailK vs0 tailBinds s1 s2 (.val tailValues)
                ⟨bindRun, tailRun, nEq, tailLift⟩
            have resVal : ∃ bindVals, res = .val bindVals := by
              cases res with
              | err e => have impossible := errEq e rfl; cases impossible
              | val bindVals => exact ⟨bindVals, rfl⟩
            obtain ⟨bindVals, rfl⟩ := resVal
            refine ⟨.val bindVals, bindsRun, by simp, ?_⟩
            intro ws s3 bindVals' eq
            cases eq
            obtain ⟨vs, vsEq, tailEval⟩ := values ws s3 bindVals rfl
            cases vsEq
            have literalEval := evalDont x env (bindVals ++ ws) s1 s1 s3 v ⟨headRun, literal⟩
            refine ⟨v :: tailValues, rfl, ?_⟩
            rw [ClosProps.evaluate_cons_value x tailYs (bindVals ++ ws) s3 s3 v literalEval,
              tailEval]


end Flapjack.Compiler.Backend.ClosOp
