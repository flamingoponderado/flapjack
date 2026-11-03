import Flapjack.Compiler.Backend.ClosOp.Proofs.Matchers
import Flapjack.Compiler.Backend.ClosLang.Pure

/-! Source lifting invariants from the corresponding HOL proof script. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang
/-- Exactly the source literal forms are exempt from lifting. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dont_lift_thm"]
theorem dontLiftCharacterization (x : Exp) :
    dontLift x = true ↔
      (∃ t i, x = .op t (.intOp (.const i)) []) ∨
      (∃ t n, x = .op t (.blockOp (.cons n)) []) ∨
      (∃ t s, x = .op t (.blockOp (.constant (.constStr s))) []) ∨
      (∃ t i, x = .op t (.blockOp (.constant (.constInt i))) []) ∨
      (∃ t w, x = .op t (.blockOp (.constant (.constWord64 w))) []) := by
  change ((destOpNil destConst x).isSome || (destOpNil destCons x).isSome ||
    (destOpNil destConstant x).isSome) = true ↔ _
  rw [destOpConst_eq_previous, destOpConsNil_eq_previous, destOpConstant_eq_previous]
  cases x <;> try simp
  case op t op xs =>
    cases op <;> try simp
    case intOp i => cases i <;> cases xs <;> simp
    case blockOp b =>
      cases b <;> try simp
      case cons tag => cases xs <;> simp
      case constant v => cases v <;> cases xs <;> simp

/-- Every expression exempt from lifting is pure. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dont_lift_pure"]
theorem dontLiftPure (x : Exp) (h : dontLift x = true) : pure x = true := by
  rcases (dontLiftCharacterization x).mp h with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩ <;>
    rfl

/-- Stronger projection form used by the source length theorem. This is
Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem liftLen (xs : List Exp) (n : Nat) (binds : List Exp) :
    (liftExpsHOL xs n binds).1.length = xs.length := by
  fun_induction liftExpsHOL xs n binds <;> simp_all

/-- A generalized index/accumulator invariant used by the source theorem.
This is Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem liftN (xs : List Exp) (n : Nat) (binds : List Exp) :
    (liftExpsHOL xs n binds).2.1 + binds.length = n + (liftExpsHOL xs n binds).2.2.length := by
  fun_induction liftExpsHOL xs n binds <;> simp_all <;> omega

/-- Projection form of accumulator extension. This is Flapjack proof
infrastructure, not a separate HOL theorem. -/
private theorem liftAcc (xs : List Exp) (n : Nat) (binds : List Exp) :
    ∃ extra, (liftExpsHOL xs n binds).2.2 = binds ++ extra := by
  fun_induction liftExpsHOL xs n binds <;> simp_all [List.append_assoc]
  case case3 =>
    rename_i x xs n binds tag ys xs1 n1 binds1 xs2 n2 binds2 hd hc hy hx ihy ihx
    obtain ⟨p, hp⟩ := ihy
    obtain ⟨q, hq⟩ := ihx
    exact ⟨p ++ q, by simp_all [List.append_assoc]⟩
  case case4 =>
    rename_i x xs n binds xs1 n1 binds1 hd hc hx ih
    obtain ⟨p, hp⟩ := ih
    exact ⟨x :: p, hp⟩
/-- Lifting extends the incoming accumulator by some suffix. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_acc"]
theorem liftExpsAcc (xs : List Exp) (n : Nat) (binds ys : List Exp) (k : Nat) (binds2 : List Exp)
    (h : liftExpsHOL xs n binds = (ys, k, binds2)) : ∃ binds1, binds2 = binds ++ binds1 := by
  have acc := liftAcc xs n binds
  rw [h] at acc
  exact acc

/-- A consistent starting index remains the length of the resulting bindings. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_n"]
theorem liftExpsN (xs : List Exp) (n : Nat) (binds ys : List Exp) (k : Nat) (binds2 : List Exp)
    (h : liftExpsHOL xs n binds = (ys, k, binds2) ∧ n = binds.length) : k = binds2.length := by
  have inv := liftN xs n binds
  rw [h.1] at inv
  simp only at inv
  omega

/-- Lifting preserves the length of the expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_length"]
theorem liftExpsLength (xs : List Exp) (n : Nat) (binds ys : List Exp) (k : Nat) (binds2 : List Exp)
    (h : liftExpsHOL xs n binds = (ys, k, binds2)) : xs.length = ys.length := by
  have len := liftLen xs n binds
  rw [h] at len
  exact len.symm

end Flapjack.Compiler.Backend.ClosOp
