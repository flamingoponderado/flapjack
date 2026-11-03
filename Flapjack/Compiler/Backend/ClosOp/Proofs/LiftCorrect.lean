import Flapjack.Compiler.Backend.ClosOp.Proofs.Matchers
import Flapjack.Compiler.Backend.ClosLang.Pure

/-! Source lifting invariants from the corresponding HOL proof script. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- The source relation for expressions whose evaluation is simple and pure. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "simple_exp"]
inductive SimpleExp : Exp → Prop where
  | var t i : SimpleExp (.var t i)
  | ite t x y z : SimpleExp x → SimpleExp y → SimpleExp z → SimpleExp (.ifThenElse t x y z)
  | intConst t i : SimpleExp (.op t (.intOp (.const i)) [])
  | constInt t i : SimpleExp (.op t (.blockOp (.constant (.constInt i))) [])
  | constStr t i : SimpleExp (.op t (.blockOp (.constant (.constStr i))) [])
  | constWord64 t i : SimpleExp (.op t (.blockOp (.constant (.constWord64 i))) [])
  | cons t i xs : (∀ x ∈ xs, SimpleExp x) → SimpleExp (.op t (.blockOp (.cons i)) xs)
  | equalInt t i x : SimpleExp x → SimpleExp (.op t (.blockOp (.equalConst (.int i))) [x])
  | equalStr t i x : SimpleExp x → SimpleExp (.op t (.blockOp (.equalConst (.str i))) [x])
  | equalWord64 t i x : SimpleExp x → SimpleExp (.op t (.blockOp (.equalConst (.w64 i))) [x])
  | elemAt t i x : SimpleExp x → SimpleExp (.op t (.blockOp (.elemAt i)) [x])
  | equal t x y : SimpleExp x → SimpleExp y → SimpleExp (.op t (.blockOp .equal) [x, y])
  | tagLenEq t l y x : SimpleExp x → SimpleExp (.op t (.blockOp (.tagLenEq l y)) [x])

/-- List form of purity, used to connect membership hypotheses to `pureList`. -/
private theorem pureListOf (xs : List Exp) (h : ∀ x ∈ xs, ClosLang.pure x = true) :
    pureList xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [pureList, Bool.and_eq_true]
    exact ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

/-- Every simple expression satisfies the source purity predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "simple_exp_pure"]
theorem simpleExpPure (x : Exp) (h : SimpleExp x) : pure x = true := by
  induction h with
  | cons t i xs hs ih =>
    simp only [ClosLang.pure, pureOp, Bool.and_true]
    exact pureListOf xs ih
  | _ => simp_all [ClosLang.pure, pureList, pureOp]
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

/-- A list of simple expressions is a list of pure expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "simple_exp_pure_every"]
theorem simpleExpPureEvery (xs : List Exp) (h : ∀ x ∈ xs, SimpleExp x) :
    ∀ x ∈ xs, pure x = true := by
  intro x hx
  exact simpleExpPure x (h x hx)

/-- The integer stage preserves simplicity; internal proof infrastructure. -/
private theorem eqDirectConstSimple (x y z : Exp) (hx : SimpleExp x) (hy : SimpleExp y)
    (h : eqDirectConst x y = some z) : SimpleExp z := by
  unfold eqDirectConst at h
  split at h <;> simp_all
  all_goals subst z
  all_goals first | exact SimpleExp.cons _ _ _ (by simp) | exact SimpleExp.equalInt _ _ _ hx | exact SimpleExp.equalInt _ _ _ hy

/-- Equality against any source constant preserves simplicity. -/
private theorem equalConstSimple (p : ConstPart) (source e : Exp)
    (hs : destOpNil destConstant source = some p) (h : SimpleExp e) :
    SimpleExp (.op .none (.blockOp (.equalConst p)) [e]) := by
  cases p with
  | con i xs =>
    rw [destOpConstant_eq_previous] at hs
    cases source <;> try simp at hs
    case op t op args =>
      cases op <;> try simp at hs
      case blockOp op =>
        cases op <;> try simp at hs
        case constant value => cases value <;> cases args <;> simp at hs
  | int i => exact SimpleExp.equalInt _ i _ h
  | str s => exact SimpleExp.equalStr _ s _ h
  | w64 w => exact SimpleExp.equalWord64 _ w _ h

/-- The constant stage preserves simplicity; internal proof infrastructure. -/
private theorem eqDirectConstantSimple (x y z : Exp) (hx : SimpleExp x) (hy : SimpleExp y)
    (h : eqDirectConstant x y = some z) : SimpleExp z := by
  unfold eqDirectConstant at h
  split at h <;> simp_all
  all_goals subst z
  all_goals try exact SimpleExp.cons _ _ _ (by simp)
  all_goals first | exact equalConstSimple _ _ _ (by assumption) hx | exact equalConstSimple _ _ _ (by assumption) hy

/-- The nullary-constructor stage preserves simplicity; internal proof infrastructure. -/
private theorem eqDirectNilSimple (x y z : Exp) (hx : SimpleExp x) (hy : SimpleExp y)
    (h : eqDirectNil x y = some z) : SimpleExp z := by
  unfold eqDirectNil at h
  split at h <;> simp_all
  all_goals subst z
  all_goals first | exact SimpleExp.cons _ _ _ (by simp) | exact SimpleExp.tagLenEq _ _ _ _ hx | exact SimpleExp.tagLenEq _ _ _ _ hy

/-- Direct equality simplification preserves simple expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_simple_exp"]
theorem eqDirectSimpleExp (x y z : Exp)
    (h : directEq x y = some z ∧ SimpleExp x ∧ SimpleExp y) : SimpleExp z := by
  rcases h with ⟨h, hx, hy⟩
  cases hc : eqDirectConst x y with
  | some e => simp [directEq, hc] at h; subst z; exact eqDirectConstSimple x y e hx hy hc
  | none =>
    cases hd : eqDirectConstant x y with
    | some e => simp [directEq, hc, hd] at h; subst z; exact eqDirectConstantSimple x y e hx hy hd
    | none =>
      simp [directEq, hc, hd] at h
      exact eqDirectNilSimple x y z hx hy h

/-- Projection form of the lifting invariant, for induction over the traversal. -/
private theorem liftSimple (xs : List Exp) (n : Nat) (binds : List Exp) :
    ∀ x ∈ (liftExpsHOL xs n binds).1, SimpleExp x := by
  fun_induction liftExpsHOL xs n binds <;> simp_all
  case case2 =>
    rename_i x xs n binds hd xs1 n1 binds1 hx ih
    rcases (dontLiftCharacterization x).mp hd with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩
    · exact SimpleExp.intConst _ _
    · exact SimpleExp.cons _ _ _ (by simp)
    · exact SimpleExp.constStr _ _
    · exact SimpleExp.constInt _ _
    · exact SimpleExp.constWord64 _ _
  case case3 => exact SimpleExp.cons _ _ _ (by assumption)
  case case4 => exact SimpleExp.var _ _

/-- Every expression returned by the source lifting traversal is simple. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_simple_exp"]
theorem liftExpsSimpleExp (xs : List Exp) (n : Nat) (binds ys : List Exp) (k : Nat) (binds2 : List Exp)
    (h : liftExpsHOL xs n binds = (ys, k, binds2)) : ∀ x ∈ ys, SimpleExp x := by
  have hs := liftSimple xs n binds
  rw [h] at hs
  exact hs

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
