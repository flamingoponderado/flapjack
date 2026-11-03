import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftCorrect

/-! Executable preservation for the source smart-operation definitions. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang
/-- The source lift preserves the two-element input length. This is Flapjack proof infrastructure. -/
private theorem liftTwo (x y : Exp) : ∃ a b n binds, liftExpsHOL [x,y] 0 [] = ([a,b],n,binds) := by
  generalize heq : liftExpsHOL [x,y] 0 [] = result
  obtain ⟨xs,n,binds⟩ := result
  have h : [x,y].length = xs.length := liftExpsLength [x,y] 0 [] xs n binds heq
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => exact ⟨a,b,n,binds,rfl⟩
      | cons c xs => simp at h

/-- The executed source smart operation agrees with the former checked implementation for every input. This is Flapjack preservation infrastructure, not a separate HOL theorem. -/
theorem smartSourceSame (fuel : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    smartFuelPrevious fuel trace op xs = smartFuel fuel trace op xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [smartFuelPrevious, smartFuel, smartOp, smartOp']
      cases h : cons x <;> simp
    | cons y xs =>
      cases xs with
      | cons z xs => rfl
      | nil =>
        simp only [smartFuelPrevious, smartFuel, smartOp, smartOp']
        cases h : destOpConsts x y with
        | some p => cases p; simp
        | none =>
          cases op <;> try rfl
          case blockOp b =>
            cases b <;> try rfl
            case equal =>
              simp only [eqOp]
              split <;> try rfl
              cases hd : directEq x y
              · obtain ⟨a,b,n,binds,hl⟩ := liftTwo x y
                simp [eqAny, liftBounded, hl]
              · rfl
end Flapjack.Compiler.Backend.ClosOp
