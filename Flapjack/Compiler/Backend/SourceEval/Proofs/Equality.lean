import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelation
import Flapjack.SemanticPrimitivesHOL.Operations
import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Forall2

/-! Equality facts for the source evaluator's recording simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- Natural conversion is injective on the nonnegative integers. The premises
make HOL's unspecified negative-input behavior irrelevant. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "Num_11"]
theorem numInjective (i j : Int) (premises : 0 ≤ i ∧ 0 ≤ j) :
    (i.toNat = j.toNat ↔ i = j) := by
  omega


/-- Flapjack induction motive for related equality operands. -/
private def eqPred (es : EvalOracleState) (x x' : Value) : Prop :=
  ∀ y y' b, doEq x y = .val b ∧ ValueRel es y y' → doEq x' y' = .val b

/-- Flapjack induction motive for related equality operand lists. -/
private def eqListPred (es : EvalOracleState) (xs xs' : List Value) : Prop :=
  ∀ ys ys' b, doEqList xs ys = .val b ∧ List.Forall₂ (ValueRel es) ys ys' → doEqList xs' ys' = .val b

/-- Flapjack mutual-recursion step proving the value part of the HOL theorem. -/
private theorem doEqRel (es : EvalOracleState) (x x' : Value) (related : ValueRel es x x') :
    eqPred es x x' := by
  refine ValueRel.rec (motive_1 := fun x x' _ => eqPred es x x')
    (motive_2 := fun _ _ _ => True) (motive_3 := fun xs xs' _ => eqListPred es xs xs')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ related
  · intro env env' id encoded decoded lookup related _ y y' b ⟨run, right⟩
    cases right with
    | env decoded₂ lookup₂ related₂ =>
      rename_i env₂ env₂' id₂
      have eq₁ := valueToEnvId_some encoded id decoded
      have eq₂ := valueToEnvId_some y' id₂ decoded₂
      subst encoded
      subst y'
      rcases id with ⟨a, b₁⟩
      rcases id₂ with ⟨c, d⟩
      by_cases ac : a = c <;> by_cases bd : b₁ = d <;>
        simp_all [doEq, doEqList, natToValue, litSameType, Int.ofNat_inj]
      all_goals try (have bad : (a == c) = false := beq_eq_false_iff_ne.mpr ac; simp_all)
      all_goals try (have bad : (b₁ == d) = false := beq_eq_false_iff_ne.mpr bd; simp_all)
    | _ => simp [doEq] at run
  · intro xs xs' values ih y y' b ⟨run, right⟩
    cases right with
    | @vector ys ys' others =>
      have len1 := List.Forall₂.length_eq values
      have len2 := List.Forall₂.length_eq others
      by_cases h : xs.length = ys.length
      · have h' : xs'.length = ys'.length := by omega
        simp only [doEq, if_pos h] at run
        simp only [doEq, if_pos h']
        exact ih ys ys' b ⟨run, others⟩
      · have h' : xs'.length ≠ ys'.length := by omega
        simpa [doEq, h, h'] using run
    | _ => simp [doEq] at run
  · intro xs xs' stamp values ih y y' b ⟨run, right⟩
    cases right with
    | @con ys ys' stamp' others =>
      have len1 := List.Forall₂.length_eq values
      have len2 := List.Forall₂.length_eq others
      by_cases h : stamp = stamp' ∧ xs.length = ys.length
      · have h' : stamp = stamp' ∧ xs'.length = ys'.length := ⟨h.1, by omega⟩
        simp only [doEq, if_pos h] at run
        simp only [doEq, if_pos h']
        exact ih ys ys' b ⟨run, others⟩
      · have h' : ¬ (stamp = stamp' ∧ xs'.length = ys'.length) := by
          rintro ⟨same, length⟩
          exact h ⟨same, by omega⟩
        simpa only [doEq, if_neg h, if_neg h'] using run
    | _ => simp [doEq] at run
  · intro env env' name body related _ y y' b ⟨run, right⟩
    cases right <;> simp_all [doEq]
  · intro env env' funs name related _ y y' b ⟨run, right⟩
    cases right <;> simp_all [doEq]
  · intro lit y y' b ⟨run, right⟩
    cases right <;> simp_all [doEq]
  · intro flag index y y' b ⟨run, right⟩
    cases right <;> simp_all [doEq]
  · intros; trivial
  · intro ys ys' b ⟨run, right⟩
    cases right <;> simpa [doEqList] using run
  · intro x x' xs xs' head tail headIH tailIH ys ys' b ⟨run, right⟩
    cases right with
    | nil => simpa [doEqList] using run
    | @cons y y' ys ys' yRel ysRel =>
      cases eq : doEq x y with
      | typeError => simp [doEqList, eq] at run
      | val bit =>
        have eq' := headIH y y' bit ⟨eq, yRel⟩
        cases bit with
        | false => simpa [doEqList, eq, eq'] using run
        | true =>
          have later := tailIH ys ys' b ⟨by simpa [doEqList, eq] using run, ysRel⟩
          simpa [doEqList, eq'] using later

/-- Flapjack list induction used to assemble the original second conjunct. -/
private theorem doEqListRel (es : EvalOracleState) (xs xs' : List Value)
    (related : List.Forall₂ (ValueRel es) xs xs') : eqListPred es xs xs' := by
  induction related with
  | nil =>
    intro ys ys' b ⟨run, right⟩
    cases right <;> simpa [doEqList] using run
  | @cons x x' xs xs' head tail ih =>
    intro ys ys' b ⟨run, right⟩
    cases right with
    | nil => simpa [doEqList] using run
    | @cons y y' ys ys' yRel ysRel =>
      cases eq : doEq x y with
      | typeError => simp [doEqList, eq] at run
      | val bit =>
        have eq' := doEqRel es x x' head y y' bit ⟨eq, yRel⟩
        cases bit with
        | false => simpa [doEqList, eq, eq'] using run
        | true =>
          have later := ih ys ys' b ⟨by simpa [doEqList, eq] using run, ysRel⟩
          simpa [doEqList, eq'] using later

/-- Equality on related values and lists preserves every successful result. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "do_eq"]
theorem doEq_simulation (es : EvalOracleState) :
    (∀ x y x' y' b, doEq x y = .val b ∧ ValueRel es x x' ∧ ValueRel es y y' →
      doEq x' y' = .val b) ∧
    (∀ xs ys xs' ys' b, doEqList xs ys = .val b ∧ List.Forall₂ (ValueRel es) xs xs' ∧
      List.Forall₂ (ValueRel es) ys ys' → doEqList xs' ys' = .val b) := by
  constructor
  · intro x y x' y' b ⟨run, left, right⟩
    exact doEqRel es x x' left y y' b ⟨run, right⟩
  · intro xs ys xs' ys' b ⟨run, left, right⟩
    exact doEqListRel es xs xs' left ys ys' b ⟨run, right⟩


end Flapjack.Compiler.Backend.SourceEval.Proofs
