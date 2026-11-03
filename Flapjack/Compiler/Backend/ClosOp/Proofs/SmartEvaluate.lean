import Flapjack.Compiler.Backend.ClosOp.Proofs.PureEquality

/-! Evaluation correctness of source smart-operation cases. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace SmartEvaluatePort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end SmartEvaluatePort

/-- Source lifted equality preserves evaluation. This intermediate lemma is
proof infrastructure, not a separately named HOL theorem. -/
private theorem eqAnyCorrect {C F : Type} (x y : ClosLang.Exp) (env : List Value)
    (s s1 : State C F) (res : Result (List Value) Value) (t : BackendCommon.Tra)
    (z : ClosLang.Exp)
    (run : evaluate [.op t (.blockOp .equal) [x, y]] env s = (res, s1))
    (notType : res ≠ .err (.abort .typeError)) (opt : eqAny x y = some z) :
    evaluate [z] env s = (res, s1) := by
  cases lift : liftExpsHOL [x, y] 0 [] with
  | mk ys rest =>
    cases rest with
    | mk k binds =>
      have len := liftExpsLength [x, y] 0 [] ys k binds lift
      cases ys with
      | nil => simp at len
      | cons a ys =>
        cases ys with
        | nil => simp at len
        | cons b tail =>
          cases tail with
          | cons c cs => simp at len
          | nil =>
            simp [eqAny, lift] at opt
            subst z
            rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp)] at run
            cases argsRun : evaluate [x, y] env s with
            | mk argsResult argsState =>
              obtain ⟨out, bindsRun, errorEq, values⟩ :=
                liftExpsThm [x, y] 0 [] env s [a, b] k [] binds s argsState argsResult
                  ⟨by simp [evaluate], argsRun, rfl, lift⟩
              cases argsResult with
              | err err =>
                simp only [argsRun] at run
                cases run
                have outErr : out = .err err := by
                  cases out with
                  | err e => exact (errorEq e rfl).symm
                  | val vs =>
                    obtain ⟨vs', impossible, _⟩ := values env s1 vs rfl
                    cases impossible
                subst out
                rw [evaluate, fixClock_evaluate, bindsRun]
              | val vs =>
                have valueLength := evaluate_length.1 [x, y] env s argsState vs argsRun
                cases vs with
                | nil => simp at valueLength
                | cons v1 vs =>
                  cases vs with
                  | nil => simp at valueLength
                  | cons v2 tail =>
                    cases tail with
                    | cons v3 rest => simp at valueLength
                    | nil =>
                      have outVal : ∃ bindVals, out = .val bindVals := by
                        cases out with
                        | err e => have impossible := errorEq e rfl; cases impossible
                        | val bindVals => exact ⟨bindVals, rfl⟩
                      obtain ⟨bindVals, rfl⟩ := outVal
                      obtain ⟨vals, valsEq, reconstructed⟩ := values env argsState bindVals rfl
                      cases valsEq
                      have simple := liftExpsSimpleExp [x, y] 0 [] [a, b] k binds lift
                      have simpleA : SimpleExp a := simple a (by simp)
                      have simpleB : SimpleExp b := simple b (by simp)
                      cases comparison : doEq v2 v1 with
                      | typeError =>
                        simp [argsRun, doApp, applyBlock, comparison] at run
                        rcases run with ⟨rfl, rfl⟩
                        exact (notType rfl).elim
                      | val flag =>
                        simp [argsRun, doApp, applyBlock, comparison] at run
                        rcases run with ⟨rfl, rfl⟩
                        have symmetric : doEq v1 v2 = .val flag := by
                          rw [ClosProps.doEqSym.1, comparison]
                        have pureRun := eqPureThm a b v1 v2 (bindVals ++ env) argsState flag
                          ⟨reconstructed, simpleA, simpleB, symmetric⟩
                        rw [evaluate, fixClock_evaluate, bindsRun]
                        exact pureRun

/-- The two-integer fast path agrees with the direct equality recognizer.
This is proof infrastructure. -/
private theorem constantsDirect (x y : ClosLang.Exp) (i j : Int)
    (h : destOpConsts x y = some (i, j)) : directEq x y = some (mkBool (j == i)) := by
  cases hx : destOpNil destConst x with
  | none => simp [destOpConsts, hx] at h
  | some a =>
    cases hy : destOpNil destConst y with
    | none => simp [destOpConsts, hx, hy] at h
    | some b =>
      simp [destOpConsts, hx, hy] at h
      rcases h with ⟨rfl, rfl⟩
      have stage : eqDirectConst x y = some (mkBool (a == b)) := by
        change (match destOpNil destConst x, destOpNil destConst y with
          | some p, some q => some (mkBool (p == q))
          | some p, none => some (.op .none (.blockOp (.equalConst (.int p))) [y])
          | none, some q => some (.op .none (.blockOp (.equalConst (.int q))) [x])
          | none, none => none) = _
        rw [hx, hy]
      have symmetric : (a == b) = (b == a) := by
        by_cases eq : a = b
        · subst b; simp
        · have rev : b ≠ a := Ne.symm eq
          simp [beq_eq_false_iff_ne.mpr eq, beq_eq_false_iff_ne.mpr rev]
      simp [directEq, stage, symmetric]

/-- Equality-operation case of the original smart-operation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmEqual {C F : Type} (t : BackendCommon.Tra) (x y : ClosLang.Exp)
    (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (h : evaluate [.op t (.blockOp .equal) [x, y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t (.blockOp .equal) [x, y]] env s = (res, s1) := by
  cases consts : destOpConsts x y with
  | some pair =>
    obtain ⟨i, j⟩ := pair
    have direct := constantsDirect x y i j consts
    have result := eqDirectThm x y env s res s1 t (mkBool (j == i)) ⟨h.1, h.2, direct⟩
    simpa [smartOp, smartOp', consts, integerOp] using result
  | none =>
    cases vars : (isVar x && isVar y) with
    | true => simpa [smartOp, smartOp', consts, eqOp, vars] using h.1
    | false =>
      cases direct : directEq x y with
      | some z =>
        have result := eqDirectThm x y env s res s1 t z ⟨h.1, h.2, direct⟩
        simpa [smartOp, smartOp', consts, eqOp, vars, direct] using result
      | none =>
        cases any : eqAny x y with
        | some z =>
          have result := eqAnyCorrect x y env s s1 res t z h.1 h.2 any
          simpa [smartOp, smartOp', consts, eqOp, vars, direct, any] using result
        | none => simpa [smartOp, smartOp', consts, eqOp, vars, direct, any] using h.1

/-- Empty-operand case of the source smart-operation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmNil {C F : Type} (t : BackendCommon.Tra) (op : ClosLang.Op)
    (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (h : evaluate [.op t op []] env s = (res, s1) ∧ res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t op []] env s = (res, s1) := by
  simpa [smartOp, smartOp'] using h.1

/-- The source smart operation leaves lists of three or more operands intact. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmMany {C F : Type} (t : BackendCommon.Tra) (op : ClosLang.Op)
    (x y z : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (h : evaluate [.op t op (x :: y :: z :: xs)] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t op (x :: y :: z :: xs)] env s = (res, s1) := by
  simpa [smartOp, smartOp'] using h.1

/-- A unary operand that does not match a constructor is left intact. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmUnaryNoConstructor {C F : Type} (t : BackendCommon.Tra) (op : ClosLang.Op)
    (x : ClosLang.Exp) (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (noConstructor : cons x = none)
    (h : evaluate [.op t op [x]] env s = (res, s1) ∧ res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t op [x]] env s = (res, s1) := by
  simpa [smartOp, smartOp', noConstructor] using h.1

/-- Literal integer evaluation used by the binary constant-folding case. -/
private theorem evalIntLiteral {C F : Type} (t : BackendCommon.Tra) (i : Int)
    (env : List Value) (s : State C F) :
    evaluate [.op t (.intOp (.const i)) []] env s = (.val [.number i], s) := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp)]
  simp [evaluate, doApp, applyNumeric, doIntApp]

/-- Source boolean construction used by constant folding. -/
private theorem evalBoolLiteral {C F : Type} (b : Bool) (env : List Value) (s : State C F) :
    evaluate [mkBool b] env s = (.val [boolValue b], s) := by
  cases b <;> rw [mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)] <;>
    simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag, BackendCommon.trueTag]

/-- The source integer matcher identifies a literal expression. -/
private theorem intSome (x : ClosLang.Exp) (i : Int) (h : destOpNil destConst x = some i) :
    ∃ t, x = .op t (.intOp (.const i)) [] := by
  rw [destOpConst_eq_previous] at h
  cases x <;> try simp at h
  case op t op xs =>
    cases op <;> try simp at h
    case intOp io =>
      cases io <;> try simp at h
      case const j => cases xs <;> simp_all

/-- Binary integer case of the source smart-operation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmInteger {C F : Type} (t : BackendCommon.Tra) (op : ClosLang.IntOp)
    (x y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value)
    (h : evaluate [.op t (.intOp op) [x, y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t (.intOp op) [x, y]] env s = (res, s1) := by
  cases consts : destOpConsts x y with
  | none => simpa [smartOp, smartOp', consts] using h.1
  | some pair =>
    obtain ⟨i, j⟩ := pair
    cases hx : destOpNil destConst x with
    | none => simp [destOpConsts, hx] at consts
    | some a =>
      cases hy : destOpNil destConst y with
      | none => simp [destOpConsts, hx, hy] at consts
      | some b =>
        simp [destOpConsts, hx, hy] at consts
        rcases consts with ⟨rfl, rfl⟩
        obtain ⟨tx, rfl⟩ := intSome x a hx
        obtain ⟨ty, rfl⟩ := intSome y b hy
        have operands : evaluate [.op tx (.intOp (.const a)) [], .op ty (.intOp (.const b)) []]
            env s = (.val [.number a, .number b], s) := by
          rw [ClosProps.evaluate_cons_value _ _ env s s (.number a) (evalIntLiteral tx a env s),
            evalIntLiteral ty b env s]
        rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp), operands] at h
        cases op <;> simp [smartOp, smartOp', destOpConsts, hx, hy, integerOp, mkInt,
          evalIntLiteral, evalBoolLiteral, doApp, applyNumeric, doIntApp] at h ⊢
        all_goals try exact h.1
        all_goals try exact (h.2 h.1.1.symm).elim
        all_goals by_cases zero : a = 0 <;> simp [zero] at h ⊢
        all_goals try exact h.1
        all_goals exact (h.2 h.1.1.symm).elim

/-- Other binary operations are unchanged by the source smart operation. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmOtherBinary {C F : Type} (t : BackendCommon.Tra) (op : ClosLang.Op)
    (x y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value)
    (notInt : ∀ i, op ≠ .intOp i) (notEqual : op ≠ .blockOp .equal)
    (h : evaluate [.op t op [x, y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t op [x, y]] env s = (res, s1) := by
  cases found : destOpConsts x y with
  | none =>
    cases op <;> try simp_all [smartOp, smartOp']
  | some pair =>
    obtain ⟨i, j⟩ := pair
    cases op <;> try simp_all [smartOp, smartOp', integerOp]

/-- Complete two-operand case of the source smart-operation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem smartOpThmBinary {C F : Type} (t : BackendCommon.Tra) (op : ClosLang.Op)
    (x y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value)
    (h : evaluate [.op t op [x, y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError)) :
    evaluate [smartOp t op [x, y]] env s = (res, s1) := by
  cases op with
  | intOp i => exact smartOpThmInteger t i x y env s s1 res h
  | blockOp block =>
    cases block
    case equal => exact smartOpThmEqual t x y env s s1 res h
    all_goals apply smartOpThmOtherBinary t _ x y env s s1 res <;> simp_all
  | _ => apply smartOpThmOtherBinary t _ x y env s s1 res <;> simp_all

end Flapjack.Compiler.Backend.ClosOp
