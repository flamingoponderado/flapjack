import Flapjack.Compiler.Backend.BvlJump
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Simulation facts for the balanced BVL dispatcher. The BVL evaluator and
its carriers still need HOL correspondence review, so these helpers are not
tagged as ports of the original proof. -/
namespace Flapjack.Compiler.Backend.BvlJump
open Flapjack.SemanticPrimitivesHOL

/-- A generated jump tree selects the indexed branch in the same state and
environment when its selector lies within the branch list. -/
theorem evaluate_jumpList {C F : Type} (n : Nat) (xs : List Bvl.Exp) (k : Nat)
    (env : List BvlSem.Value) (s : BvlSem.State C F) (bound : k < xs.length) :
    BvlSem.evaluate [jumpList n xs] (.number (Int.ofNat (n + k)) :: env) s =
      BvlSem.evaluate [xs[k]] (.number (Int.ofNat (n + k)) :: env) s := by
  cases xs with
  | nil => simp at bound
  | cons first rest =>
    cases rest with
    | nil =>
      have : k = 0 := by simp at bound; omega
      subst k
      simp [jumpList]
    | cons second rest =>
      let xs := first :: second :: rest
      let mid := xs.length / 2
      have bound' : k < xs.length := by simpa [xs] using bound
      have midPositive : 0 < mid := by dsimp [mid, xs]; omega
      have midLess : mid < xs.length := by dsimp [mid, xs]; omega
      have smallOrLarge : n + xs.length < 1000000 ∧ n + mid < 1000000 ∨
          ¬ (n + xs.length < 1000000 ∧ n + mid < 1000000) := by exact em _
      have testRun : BvlSem.evaluate
          [if n + xs.length < 1000000 ∧ n + mid < 1000000 then
            .op (.intOp (.lessConstSmall (n + mid))) [.var 0]
           else .op (.intOp .less) [.op (.intOp (.const (Int.ofNat (n + mid)))) [], .var 0]]
          (.number (Int.ofNat (n + k)) :: env) s =
          (.val [BvlSem.boolValue (decide (k < mid))], s) := by
        rcases smallOrLarge with small | large
        · have selectorBound : n + k ≤ 1000000 := by omega
          have selectorInt : (Int.ofNat n + Int.ofNat k) ≤ 1000000 := by
            have h : Int.ofNat (n + k) ≤ Int.ofNat 1000000 := Int.ofNat_le.mpr selectorBound
            simpa [Int.ofNat_eq_natCast] using h
          have selectorNonnegative : (0 : Int) ≤ (n : Int) + (k : Int) := by omega
          simp only [Int.ofNat_eq_natCast] at selectorInt selectorNonnegative
          simp [small, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
            BvlSem.doIntApp]
          simp only [selectorInt, selectorNonnegative, true_and, ↓reduceIte]
        · simp [large, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
            BvlSem.doIntApp]
      change BvlSem.evaluate [jumpList n xs] (.number (Int.ofNat (n + k)) :: env) s = _
      rw [jumpList]
      change BvlSem.evaluate [.ifThenElse _ (jumpList n (xs.take mid)) (jumpList (n + mid) (xs.drop mid))] _ s = _
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, testRun]
      by_cases left : k < mid
      · simp only [left, decide_true, BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.trueTag, BvlSem.asBool]
        have takeBound : k < (xs.take mid).length := by simp [List.length_take]; omega
        rw [evaluate_jumpList n (xs.take mid) k env s takeBound]
        simp [List.getElem_take, xs]
      · simp only [left, decide_false, BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.falseTag, BvlSem.asBool]
        have dropBound : k - mid < (xs.drop mid).length := by simp [List.length_drop]; omega
        have indexEq : n + mid + (k - mid) = n + k := by omega
        have step := evaluate_jumpList (n + mid) (xs.drop mid) (k - mid) env s dropBound
        simp only [indexEq, List.getElem_drop] at step
        simpa [xs, show mid + (k - mid) = k by omega] using step
termination_by xs.length
decreasing_by
  all_goals
    try simp_wf
    simp_all [List.length_take, List.length_drop]
    omega

/-- Evaluating the selector and generated jump enters the indexed branch. -/
theorem evaluate_jump {C F : Type} (selector : Bvl.Exp) (xs : List Bvl.Exp)
    (env : List BvlSem.Value) (s next : BvlSem.State C F) (n : Nat)
    (selectorRun : BvlSem.evaluate [selector] env s = (.val [.number (Int.ofNat n)], next))
    (bound : n < xs.length) :
    BvlSem.evaluate [jump selector xs] env s =
      BvlSem.evaluate [xs[n]] (.number (Int.ofNat n) :: env) next := by
  rw [jump, BvlSem.evaluate, BvlSem.fixClock_evaluate, selectorRun]
  simpa using evaluate_jumpList 0 xs n env next bound

end Flapjack.Compiler.Backend.BvlJump
