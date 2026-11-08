import Flapjack.Compiler.Backend.ClosCall.Calls
import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed
import Flapjack.Compiler.Backend.ClosKnown.Inline.Free.Correct

/-! Connecting the bounded executable traversal to the total HOL traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

/-- Pairwise total closedness test used by the direct-call group case. This
Flapjack helper factors the paired predicate appearing inline in HOL. -/
private def totalGroupClosed (pairs : List ((Nat × Exp) × Exp)) : Bool :=
  pairs.all (fun (fn, code) =>
    closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code))

private theorem groupClosedFold_eq (fuel : Nat) (pairs : List ((Nat × Exp) × Exp)) (initial : Bool) :
    pairs.foldlM (fun all pair => do
      if !all then pure false else
        closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2))
      initial = some (initial && totalGroupClosed pairs) := by
  induction pairs generalizing initial with
  | nil => cases initial <;> rfl
  | cons pair rest ih =>
    cases initial with
    | false => simpa [totalGroupClosed] using ih false
    | true =>
      simp only [List.foldlM_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        ClosKnown.closedFuel_correct, Option.bind_eq_bind, Option.bind_some, totalGroupClosed,
        List.all_cons, Bool.true_and]
      cases h : closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2) with
      | false => simpa [totalGroupClosed, h, ClosKnown.closedFuel_correct] using ih false
      | true => simpa [totalGroupClosed, h, ClosKnown.closedFuel_correct] using ih true

/-- The executed group fold agrees with the total pairwise closedness test.
This Flapjack bridge is needed to compare the bounded and total traversals. -/
theorem groupClosedFuel_eq_total (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp) :
    groupClosedFuel fuel fns bodies = some ((fns.zip bodies).all (fun (fn, code) =>
      closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code))) := by
  simpa [groupClosedFuel, totalGroupClosed] using groupClosedFold_eq fuel (fns.zip bodies) true

end Flapjack.Compiler.Backend.ClosCall
