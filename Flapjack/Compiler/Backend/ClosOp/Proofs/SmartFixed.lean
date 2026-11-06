import Flapjack.Compiler.Backend.ClosOp.Proofs.ReductionInvariants
import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

/-! Source smart-operation cases that retain the original expression. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- Shared case split for unchanged operations; Flapjack proof infrastructure, not a HOL theorem. -/
private theorem fixed (t : BackendCommon.Tra) (op : Op) (xs : List Exp)
    (hc : ∀ tag args, consOp op tag args = none)
    (hi : ∀ i j, integerOp op i j = none)
    (he : op ≠ .blockOp .equal) : smartOp t op xs = .op t op xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [smartOp, smartOp']
      cases h : cons x with
      | none => rfl
      | some p => obtain ⟨tag,args⟩ := p; simp [hc]
    | cons y xs =>
      cases xs with
      | cons z xs => rfl
      | nil =>
        simp only [smartOp, smartOp']
        cases h : destOpConsts x y with
        | some p => obtain ⟨i,j⟩ := p; simp [hi]
        | none =>
          cases op <;> try rfl

/-- A constant operation is unchanged by the smart constructor. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_Const"]
theorem smartConst (t : BackendCommon.Tra) (i : Int) (xs : List Exp) :
    smartOp t (.intOp (.const i)) xs = .op t (.intOp (.const i)) xs := by
  apply fixed
  · intro tag args; rfl
  · intro a b; rfl
  · simp

/-- A constructor operation is unchanged by the smart constructor. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_Cons"]
theorem smartCons (t : BackendCommon.Tra) (n : Nat) (xs : List Exp) :
    smartOp t (.blockOp (.cons n)) xs = .op t (.blockOp (.cons n)) xs := by
  apply fixed
  · intro tag args; rfl
  · intro a b; rfl
  · simp

/-- The smart constructor is the original installation operation as a function. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "SmartOp_Install"]
theorem smartInstall (t : BackendCommon.Tra) :
    smartOp t .install = Exp.op t .install := by
  funext xs
  apply fixed
  · intro tag args; rfl
  · intro a b; rfl
  · simp
/-- Reduction preserves location order; this stronger Flapjack lemma has no separate HOL declaration. -/
theorem redCodeLocations (xs ys : List Exp) (h : RedRel xs ys) :
    ClosProps.codeLocations xs = ClosProps.codeLocations ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    simpa [ClosProps.codeLocations, ClosProps.codeLocationsExp] using ih
  | nil => rfl
  | refl x => rfl
  | var v t => rfl
  | multi x y zs x1 x2 hx hy ihx ihy =>
    simp_all [ClosProps.codeLocations, ClosProps.codeLocations_append]
  | letE xs x x1 t hx hy ihx ihy =>
    simp_all [ClosProps.codeLocations, ClosProps.codeLocationsExp]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz =>
    simp_all [ClosProps.codeLocations, ClosProps.codeLocationsExp,
      ClosProps.codeLocations_append, List.append_assoc]

/-- Smart operations preserve location order; this stronger Flapjack lemma has no separate HOL declaration. -/
theorem smartCodeLocations (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    ClosProps.codeLocations [smartOp t op xs] = ClosProps.codeLocations [.op t op xs] := by
  obtain ⟨ys,h1,h2⟩ := smartRed t op xs
  exact (redCodeLocations _ _ h2).trans (redCodeLocations _ _ h1).symm

/-- Smart operations preserve the bag of code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "code_locs_SmartOp"]
theorem smartCodeBag (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    (fun n : Nat => (ClosProps.codeLocations [smartOp t op xs]).count n) =
      (fun n : Nat => (ClosProps.codeLocations [.op t op xs]).count n) := by
  rw [smartCodeLocations]
end Flapjack.Compiler.Backend.ClosOp
