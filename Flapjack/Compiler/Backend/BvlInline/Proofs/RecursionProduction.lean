import Flapjack.Compiler.Backend.BvlInline.Recursion
import Flapjack.Compiler.Backend.BvlInline.Proofs.SmallProduction

/-! Correspondence between executed and total BVL inlining tests. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

private theorem foldRec_eq {α : Type} (xs : List α) (visit : α → Option Bool)
    (predicate : α → Bool) (correct : ∀ x value, visit x = some value → value = predicate x)
    (found result : Bool)
    (run : xs.foldlM (fun found x => if found then pure true else visit x) found = some result) :
    result = (found || xs.any predicate) := by
  induction xs generalizing found result with
  | nil => simpa using run.symm
  | cons x xs ih =>
    cases found with
    | true =>
      have tail : xs.foldlM (fun found x => if found then pure true else visit x) true = some result := by
        simpa using run
      simpa using ih true result tail
    | false =>
      cases first : visit x with
      | none => simp [first] at run
      | some value =>
        have tail : xs.foldlM (fun found x => if found then pure true else visit x) value = some result := by
          simpa [first] using run
        have eq := ih value result tail
        have head := correct x value first
        subst value
        simpa using eq

/-- Every successful fuel-bounded recursion check agrees with the total
source test. This executable correspondence has no standalone HOL original. -/
theorem recursiveFuel_eq (fuel name : Nat) (e : Exp) (result : Bool)
    (run : recursiveFuel fuel name e = some result) : result = isRecSing name e := by
  induction fuel generalizing e result with
  | zero => simp [recursiveFuel] at run
  | succ fuel ih =>
    cases e with
    | var v => simpa [recursiveFuel, isRecSing] using run.symm
    | force a b => simpa [recursiveFuel, isRecSing] using run.symm
    | tick e => simpa [isRecSing] using ih e result (by simpa [recursiveFuel] using run)
    | raise e => simpa [isRecSing] using ih e result (by simpa [recursiveFuel] using run)
    | ifThenElse x y z =>
      have eq := foldRec_eq [x, y, z] (recursiveFuel fuel name) (isRecSing name) ih false result
        (by simpa [recursiveFuel] using run)
      simpa [isRecSing, Bool.or_assoc] using eq
    | «let» xs body =>
      have eq := foldRec_eq (xs ++ [body]) (recursiveFuel fuel name) (isRecSing name) ih false result
        (by simpa [recursiveFuel] using run)
      simpa [isRecSing, isRecList_eq_any] using eq
    | handle x y =>
      have eq := foldRec_eq [x, y] (recursiveFuel fuel name) (isRecSing name) ih false result
        (by simpa [recursiveFuel] using run)
      simpa [isRecSing] using eq
    | op op xs =>
      have eq := foldRec_eq xs (recursiveFuel fuel name) (isRecSing name) ih false result
        (by simpa [recursiveFuel] using run)
      simpa [isRecSing, isRecList_eq_any] using eq
    | call ticks dest xs =>
      cases equal : (dest == some name) with
      | true => simpa [recursiveFuel, isRecSing, equal] using run.symm
      | false =>
        have eq := foldRec_eq xs (recursiveFuel fuel name) (isRecSing name) ih false result
          (by simpa [recursiveFuel, equal] using run)
        simpa [isRecSing, equal, isRecList_eq_any] using eq

/-- The production recursion retry always returns the source recursion test.
This executable correspondence has no standalone HOL original. -/
theorem recursiveBounded_eq (fuel name : Nat) (e : Exp) :
    recursiveBounded fuel name e = some (isRecSing name e) := by
  cases first : recursiveFuel fuel name e with
  | some result =>
    have correct := recursiveFuel_eq fuel name e result first
    simp [recursiveBounded, first, correct]
  | none =>
    have bound : BvlToBvi.expBudget e < max fuel (BvlToBvi.expBudget e + 1) := by omega
    obtain ⟨result, run⟩ := recursiveFuel_succeeds _ name e bound
    have correct := recursiveFuel_eq _ name e result run
    simp [recursiveBounded, first, run, correct]

/-- The actual bounded size and recursion checks make the same cache decision
as the original `must_inline`. This executable correspondence has no
standalone HOL declaration. -/
theorem mustInline_executable_eq (fuel name limit : Nat) (e : Exp) :
    (do
      let size ← smallExpBounded fuel limit e
      let recurs ← if size == 0 then pure false else recursiveBounded fuel name e
      pure (size != 0 && !recurs)) = some (mustInline name limit e) := by
  by_cases zero : isSmallSing limit e = 0 <;>
    simp [smallExpBounded_eq, recursiveBounded_eq, mustInline, isSmall, isRec, isRecList, zero]

end Flapjack.Compiler.Backend.BvlInline
