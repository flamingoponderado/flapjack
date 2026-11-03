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


/-- General binding case of the source functional induction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_thm"
  (fmap_as_finite_support := [refs, code])]
theorem liftExpsThmBind {C F : Type} (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (n : Nat) (binds : List ClosLang.Exp) (notLiteral : dontLift x = false)
    (notCons : cons x = none) (ih : @LiftEvaluate C F xs (n + 1) (binds ++ [x])) :
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
  cases tailLift : liftExpsHOL xs (n + 1) (binds ++ [x]) with
  | mk tailYs tailPair =>
    cases tailPair with
    | mk tailK tailBinds =>
      have liftEq : (.var .none n :: tailYs, tailK, tailBinds) = (ys, k, binds2) := by
        simp [liftExpsHOL, notLiteral, tailLift] at lifted
        split at lifted
        next tag args hc => simp_all
        next hc => exact lifted
      simp only [Prod.mk.injEq] at liftEq
      rcases liftEq with ⟨rfl, rfl, rfl⟩
      obtain ⟨extra, extraEq⟩ := liftExpsAcc xs (n + 1) (binds ++ [x])
        tailYs tailK tailBinds tailLift
      cases headRun : evaluate [x] env s1 with
      | mk headResult headState =>
        cases headResult with
        | err err =>
          have headError := ClosProps.evaluate_cons_error x xs env s1 headState err headRun
          rw [headError] at run
          cases run
          have bindsError : evaluate tailBinds env s0 = (.err err, s2) := by
            rw [extraEq, List.append_assoc, ClosProps.evaluateAppend, bindRun]
            simp [ClosProps.evaluate_cons_error x extra env s1 s2 err headRun]
          exact ⟨.err err, bindsError, by simp, by simp⟩
        | val headValues =>
          obtain ⟨value, rfl⟩ := evaluate_singleton_value x env s1 headState headValues headRun
          have bindsSuccess : evaluate (binds ++ [x]) env s0 = (.val (vs0 ++ [value]), headState) := by
            rw [ClosProps.evaluateAppend]
            simp [bindRun, headRun]
          rw [ClosProps.evaluate_cons_value x xs env s1 headState value headRun] at run
          cases tailRun : evaluate xs env headState with
          | mk tailResult tailState =>
            cases tailResult with
            | err err =>
              simp only [tailRun] at run
              cases run
              obtain ⟨res, bindsRun, errEq, values⟩ :=
                ih env s0 tailYs tailK (vs0 ++ [value]) tailBinds headState s2 (.err err)
                  ⟨bindsSuccess, tailRun, by simp [nEq], tailLift⟩
              refine ⟨res, bindsRun, errEq, ?_⟩
              intro ws s3 bindVals resEq
              obtain ⟨vs, impossible, _⟩ := values ws s3 bindVals resEq
              cases impossible
            | val tailValues =>
              simp only [tailRun] at run
              cases run
              obtain ⟨res, bindsRun, errEq, values⟩ :=
                ih env s0 tailYs tailK (vs0 ++ [value]) tailBinds headState s2 (.val tailValues)
                  ⟨bindsSuccess, tailRun, by simp [nEq], tailLift⟩
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
              have valuePrefix : ∃ rest, bindVals = (vs0 ++ [value]) ++ rest := by
                rw [extraEq, ClosProps.evaluateAppend, bindsSuccess] at bindsRun
                cases extraRun : evaluate extra env headState with
                | mk extraResult extraState =>
                  cases extraResult with
                  | err err => simp [extraRun] at bindsRun
                  | val rest =>
                    simp only [extraRun, Prod.mk.injEq, Result.val.injEq] at bindsRun
                    exact ⟨rest, bindsRun.1.symm⟩
              obtain ⟨rest, rfl⟩ := valuePrefix
              have len : vs0.length = n := by
                have h := evaluate_length.1 binds env s0 s1 vs0 bindRun
                omega
              have varEval : evaluate [.var .none n] (((vs0 ++ [value]) ++ rest) ++ ws) s3 =
                  (.val [value], s3) := by
                simp [evaluate, ← len]
              refine ⟨value :: tailValues, rfl, ?_⟩
              rw [ClosProps.evaluate_cons_value _ _ _ s3 s3 value varEval, tailEval]

/-- Constructor evaluation first evaluates its arguments in order. This is
proof infrastructure for the constructor case, not a separate HOL theorem. -/
theorem evaluateConstructor {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (args : List ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op trace (.blockOp (.cons tag)) args] env s =
      match evaluate args env s with
      | (.err err, next) => (.err err, next)
      | (.val values, next) => (.val [.block tag values.reverse], next) := by
  rw [evaluate_ordinaryOp_eq trace _ args env s (by simp) (by simp)]
  cases h : evaluate args env s with
  | mk result next => cases result <;> simp [doApp, applyBlock]

/-- Constructor case of the original functional induction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_thm"
  (fmap_as_finite_support := [refs, code])]
theorem liftExpsThmCons {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (args xs : List ClosLang.Exp) (n : Nat) (binds : List ClosLang.Exp)
    (notLiteral : dontLift (.op trace (.blockOp (.cons tag)) args) = false)
    (ihArgs : @LiftEvaluate C F args n binds)
    (ihTail : @LiftEvaluate C F xs (liftExpsHOL args n binds).2.1
      (liftExpsHOL args n binds).2.2) :
    ∀ (env : List Value) (s0 : State C F) (ys : List ClosLang.Exp) (k : Nat)
      (vs0 : List Value) (binds2 : List ClosLang.Exp) (s1 s2 : State C F)
      (res0 : Result (List Value) Value),
      evaluate binds env s0 = (.val vs0, s1) ∧
      evaluate (.op trace (.blockOp (.cons tag)) args :: xs) env s1 = (res0, s2) ∧
      n = binds.length ∧
      liftExpsHOL (.op trace (.blockOp (.cons tag)) args :: xs) n binds = (ys, k, binds2) →
      ∃ res, evaluate binds2 env s0 = (res, s2) ∧
        (∀ err, res = .err err → res0 = res) ∧
        ∀ (ws : List Value) (s3 : State C F) (bindVals : List Value),
          res = .val bindVals → ∃ vs, res0 = .val vs ∧
            evaluate ys (bindVals ++ ws) s3 = (.val vs, s3) := by
  intro env s0 ys k vs0 binds2 s1 s2 res0 ⟨bindRun, run, nEq, lifted⟩
  cases argLift : liftExpsHOL args n binds with
  | mk argYs argPair =>
    cases argPair with
    | mk argK argBinds =>
      simp only [argLift] at ihTail
      cases tailLift : liftExpsHOL xs argK argBinds with
      | mk tailYs tailPair =>
        cases tailPair with
        | mk tailK tailBinds =>
          have liftEq : (.op .none (.blockOp (.cons tag)) argYs :: tailYs, tailK, tailBinds) =
              (ys, k, binds2) := by
            simp [liftExpsHOL, notLiteral, argLift, tailLift, cons, destOp, destCons] at lifted
            simpa only [Prod.mk.injEq] using lifted
          simp only [Prod.mk.injEq] at liftEq
          rcases liftEq with ⟨rfl, rfl, rfl⟩
          obtain ⟨extra, extraEq⟩ := liftExpsAcc xs argK argBinds tailYs tailK tailBinds tailLift
          have argKEq := liftExpsN args n binds argYs argK argBinds ⟨argLift, nEq⟩
          cases argRun : evaluate args env s1 with
          | mk argResult argState =>
            cases argResult with
            | err err =>
              have headRun : evaluate [.op trace (.blockOp (.cons tag)) args] env s1 =
                  (.err err, argState) := by rw [evaluateConstructor, argRun]
              rw [ClosProps.evaluate_cons_error _ xs env s1 argState err headRun] at run
              cases run
              obtain ⟨res, argBindsRun, errEq, values⟩ :=
                ihArgs env s0 argYs argK vs0 argBinds s1 s2 (.err err)
                  ⟨bindRun, argRun, nEq, argLift⟩
              have resErr : res = .err err := by
                cases res with
                | err e => exact (errEq e rfl).symm
                | val bindVals =>
                  obtain ⟨vs, impossible, _⟩ := values [] s2 bindVals rfl
                  cases impossible
              subst res
              have bindsError : evaluate tailBinds env s0 = (.err err, s2) := by
                rw [extraEq, ClosProps.evaluateAppend]
                simp [argBindsRun]
              exact ⟨.err err, bindsError, by simp, by simp⟩
            | val argValues =>
              have headRun : evaluate [.op trace (.blockOp (.cons tag)) args] env s1 =
                  (.val [.block tag argValues.reverse], argState) := by rw [evaluateConstructor, argRun]
              rw [ClosProps.evaluate_cons_value _ xs env s1 argState _ headRun] at run
              cases tailRun : evaluate xs env argState with
              | mk tailResult tailState =>
                cases tailResult with
                | err err =>
                  simp only [tailRun] at run
                  cases run
                  obtain ⟨res, argBindsRun, errEq, values⟩ :=
                    ihArgs env s0 argYs argK vs0 argBinds s1 argState (.val argValues)
                      ⟨bindRun, argRun, nEq, argLift⟩
                  have resVal : ∃ midVals, res = .val midVals := by
                    cases res with
                    | err e => have impossible := errEq e rfl; cases impossible
                    | val midVals => exact ⟨midVals, rfl⟩
                  obtain ⟨midVals, rfl⟩ := resVal
                  obtain ⟨out, bindsRun, errEq, tailValues⟩ :=
                    ihTail env s0 tailYs tailK midVals tailBinds argState s2 (.err err)
                      ⟨argBindsRun, tailRun, argKEq, tailLift⟩
                  refine ⟨out, bindsRun, errEq, ?_⟩
                  intro ws s3 bindVals outEq
                  obtain ⟨vs, impossible, _⟩ := tailValues ws s3 bindVals outEq
                  cases impossible
                | val tailValues =>
                  simp only [tailRun] at run
                  cases run
                  obtain ⟨res, argBindsRun, errEq, argValuesIH⟩ :=
                    ihArgs env s0 argYs argK vs0 argBinds s1 argState (.val argValues)
                      ⟨bindRun, argRun, nEq, argLift⟩
                  have resVal : ∃ midVals, res = .val midVals := by
                    cases res with
                    | err e => have impossible := errEq e rfl; cases impossible
                    | val midVals => exact ⟨midVals, rfl⟩
                  obtain ⟨midVals, rfl⟩ := resVal
                  obtain ⟨out, bindsRun, outErr, tailValuesIH⟩ :=
                    ihTail env s0 tailYs tailK midVals tailBinds argState s2 (.val tailValues)
                      ⟨argBindsRun, tailRun, argKEq, tailLift⟩
                  have outVal : ∃ bindVals, out = .val bindVals := by
                    cases out with
                    | err e => have impossible := outErr e rfl; cases impossible
                    | val bindVals => exact ⟨bindVals, rfl⟩
                  obtain ⟨bindVals, rfl⟩ := outVal
                  refine ⟨.val bindVals, bindsRun, by simp, ?_⟩
                  intro ws s3 bindVals' eq
                  cases eq
                  obtain ⟨vs, vsEq, tailEval⟩ := tailValuesIH ws s3 bindVals rfl
                  cases vsEq
                  have valuePrefix : ∃ rest, bindVals = midVals ++ rest := by
                    rw [extraEq, ClosProps.evaluateAppend, argBindsRun] at bindsRun
                    cases extraRun : evaluate extra env argState with
                    | mk extraResult extraState =>
                      cases extraResult with
                      | err err => simp [extraRun] at bindsRun
                      | val rest =>
                        simp only [extraRun, Prod.mk.injEq, Result.val.injEq] at bindsRun
                        exact ⟨rest, bindsRun.1.symm⟩
                  obtain ⟨rest, rfl⟩ := valuePrefix
                  obtain ⟨argVs, argEq, argEval⟩ := argValuesIH (rest ++ ws) s3 midVals rfl
                  cases argEq
                  have headEval : evaluate [.op .none (.blockOp (.cons tag)) argYs]
                      ((midVals ++ rest) ++ ws) s3 = (.val [.block tag argValues.reverse], s3) := by
                    rw [evaluateConstructor]
                    simp [List.append_assoc, argEval]
                  refine ⟨.block tag argValues.reverse :: tailValues, rfl, ?_⟩
                  rw [ClosProps.evaluate_cons_value _ _ _ s3 s3 _ headEval, tailEval]

/-- The source constructor matcher identifies its expression. -/
private theorem consSome (x : ClosLang.Exp) (tag : Nat) (args : List ClosLang.Exp)
    (h : cons x = some (tag, args)) :
    ∃ trace, x = .op trace (.blockOp (.cons tag)) args := by
  rw [destOpCons_eq_previous] at h
  cases x <;> try simp at h
  case op trace op es =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> simp_all

private theorem liftEvaluateAll {C F : Type} (xs : List ClosLang.Exp)
    (n : Nat) (binds : List ClosLang.Exp) : @LiftEvaluate C F xs n binds := by
  fun_induction liftExpsHOL xs n binds
  case case1 => exact liftExpsThmNil _ _
  case case2 x xs n binds hd ys k bs hl ih =>
    exact liftExpsThmDontLift x xs n binds hd ih
  case case3 x xs n binds hd tag args hc ys k bs ha zs k2 bs2 ht ihArgs ihTail =>
    obtain ⟨trace, rfl⟩ := consSome x tag args hc
    have notLiteral : dontLift (.op trace (.blockOp (.cons tag)) args) = false := by
      cases h : dontLift (.op trace (.blockOp (.cons tag)) args) <;> simp_all
    apply liftExpsThmCons trace tag args xs n binds notLiteral ihArgs
    simpa [ha] using ihTail
  case case4 x xs n binds hd hc ys k bs hl ih =>
    have notLiteral : dontLift x = false := by cases h : dontLift x <;> simp_all
    exact liftExpsThmBind x xs n binds notLiteral hc ih

/-- Expression lifting preserves evaluation, errors, and the reconstructed
values in any state and environment extending the evaluated bindings. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_thm"
  (fmap_as_finite_support := [refs, code])]
theorem liftExpsThm {C F : Type} (xs : List ClosLang.Exp) (n : Nat)
    (binds : List ClosLang.Exp) (env : List Value) (s0 : State C F)
    (ys : List ClosLang.Exp) (k : Nat) (vs0 : List Value) (binds2 : List ClosLang.Exp)
    (s1 s2 : State C F) (res0 : Result (List Value) Value)
    (h : evaluate binds env s0 = (.val vs0, s1) ∧
      evaluate xs env s1 = (res0, s2) ∧ n = binds.length ∧
      liftExpsHOL xs n binds = (ys, k, binds2)) :
    ∃ res, evaluate binds2 env s0 = (res, s2) ∧
      (∀ err, res = .err err → res0 = res) ∧
      ∀ (ws : List Value) (s3 : State C F) (bindVals : List Value),
        res = .val bindVals → ∃ vs, res0 = .val vs ∧
          evaluate ys (bindVals ++ ws) s3 = (.val vs, s3) :=
  liftEvaluateAll xs n binds env s0 ys k vs0 binds2 s1 s2 res0 h

/-- A lifted singleton under a let has the original evaluation. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_Let"
  (fmap_as_finite_support := [refs, code])]
theorem liftExpsLet {C F : Type} (x y : ClosLang.Exp) (n : Nat)
    (binds : List ClosLang.Exp) (env : List Value) (s1 s2 : State C F)
    (res : Result (List Value) Value)
    (h : liftExpsHOL [x] 0 [] = ([y], n, binds) ∧
      evaluate [x] env s1 = (res, s2)) :
    evaluate [.let .none binds y] env s1 = (res, s2) := by
  obtain ⟨out, bindsRun, errorEq, values⟩ :=
    liftExpsThm [x] 0 [] env s1 [y] n [] binds s1 s2 res
      ⟨by simp [evaluate], h.2, rfl, h.1⟩
  rw [evaluate, fixClock_evaluate, bindsRun]
  cases out with
  | err err =>
    have eq := errorEq err rfl
    rw [eq]
  | val bindVals =>
    obtain ⟨vs, eq, bodyRun⟩ := values env s2 bindVals rfl
    simpa [eq] using bodyRun

end Flapjack.Compiler.Backend.ClosOp
