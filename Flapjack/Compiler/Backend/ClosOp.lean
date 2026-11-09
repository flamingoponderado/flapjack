module

public import Flapjack.Compiler.Backend.ClosLang.Budget
public import Flapjack.Compiler.Backend.ClosOp.EqBudget
public import Flapjack.Compiler.Backend.ClosOp.EqWeightProofs
public import Flapjack.Misc.AppList

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Bounded infrastructure for the closure smart-operation pass. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

private def intConst : Exp → Option Int := destOpNil destConst
private def nil : Exp → Option Nat := destOpNil destCons
private def constant : Exp → Option ConstPart := destOpNil destConstant

private def eqConst (p : ConstPart) (x : Exp) : Exp := .op .none (.blockOp (.equalConst p)) [x]

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_const_def"]
def eqDirectConst (x y : Exp) : Option Exp :=
  match intConst x, intConst y with
  | some i, some j => some (mkBool (i == j))
  | some i, none => some (eqConst (.int i) y)
  | none, some j => some (eqConst (.int j) x)
  | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_constant_def"]
def eqDirectConstant (x y : Exp) : Option Exp :=
  match constant x, constant y with
  | some p, some q => some (mkBool (decide (q = p)))
  | some p, none => some (eqConst p y)
  | none, some q => some (eqConst q x)
  | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_nil_def"]
def eqDirectNil (x y : Exp) : Option Exp :=
  match nil x, nil y with
  | some i, some j => some (mkBool (i == j))
  | some i, none => some (.op .none (.blockOp (.tagLenEq i 0)) [y])
  | none, some j => some (.op .none (.blockOp (.tagLenEq j 0)) [x])
  | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_def"]
def directEq (x y : Exp) : Option Exp :=
  match eqDirectConst x y with
  | some result => some result
  | none =>
    match eqDirectConstant x y with
    | some result => some result
    | none => eqDirectNil x y

@[hol "cakeml/compiler/backend/clos_opScript.sml" "int_op_def"]
def integerOp (op : Op) (i j : Int) : Option Exp :=
  match op with
  | .intOp .add => some (mkInt (j + i))
  | .intOp .sub => some (mkInt (j - i))
  | .intOp .mult => some (mkInt (j * i))
  | .intOp .div => some (mkInt (if i == 0 then 0 else Int.fdiv j i))
  | .intOp .mod => some (mkInt (if i == 0 then 0 else Int.fmod j i))
  | .intOp .less => some (mkBool (j < i))
  | .intOp .lessEq => some (mkBool (j ≤ i))
  | .intOp .greater => some (mkBool (i < j))
  | .intOp .greaterEq => some (mkBool (i ≤ j))
  | .blockOp .equal => some (mkBool (j == i))
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "cons_op_def"]
def consOp (op : Op) (tag : Nat) (xs : List Exp) : Option Exp :=
  match destElemAt op with
  | some n =>
      if n < xs.length then some (.let .none xs (.var .none (xs.length - (n + 1)))) else none
  | none =>
    match destTagLenEq op with
    | some (n, len) => some (.let .none xs (mkBool (n == tag && xs.length == len)))
    | none =>
      match destTagEq op with
      | some n => some (.let .none xs (mkBool (n == tag)))
      | none =>
        match destLenEq op with
        | some len => some (.let .none xs (mkBool (xs.length == len)))
        | none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dont_lift_def"]
def dontLift (e : Exp) : Bool := (intConst e).isSome || (nil e).isSome || (constant e).isSome

/-- Structural decrease for a matched constructor; this is Flapjack
termination infrastructure rather than a separate HOL theorem. -/
private theorem consBudgetOfSome (x : Exp) (tag : Nat) (ys : List Exp)
    (h : cons x = some (tag, ys)) : listBudget ys < expBudget x := by
  cases x <;> simp [cons, destOp] at h
  case op t op args =>
    cases op <;> try simp [destCons] at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons tag =>
        rcases h with ⟨rfl, rfl⟩
        simp [expBudget]

/-- Lift effectful expressions in source order, threading index and bindings. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "lift_exps_def"]
def liftExpsHOL : List Exp → Nat → List Exp → List Exp × Nat × List Exp
  | [], n, binds => ([], n, binds)
  | x :: xs, n, binds =>
    if dontLift x then
      let (xs, n, binds) := liftExpsHOL xs n binds
      (x :: xs, n, binds)
    else match _hc : cons x with
      | some (tag, ys) =>
          let (ys, n, binds) := liftExpsHOL ys n binds
          let (xs, n, binds) := liftExpsHOL xs n binds
          (.op .none (.blockOp (.cons tag)) ys :: xs, n, binds)
      | none =>
          let (xs, next, binds) := liftExpsHOL xs (n + 1) (binds ++ [x])
          (.var .none n :: xs, next, binds)
termination_by xs _ _ => listBudget xs
decreasing_by
  all_goals simp_wf
  all_goals try (simp [listBudget]; omega)
  all_goals
    have h := consBudgetOfSome x _ _ _hc
    simp [listBudget]
    omega

/-- Source equality decomposition, retaining its append-tree structure. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_pure_list_def"]
def eqPureList : List (Exp × Exp) → AppList Exp
  | [] => .nil
  | [(x, y)] =>
    match directEq x y with
    | some e => .list [e]
    | none =>
      match _hx : cons x, _hy : cons y with
      | none, none => .list [.op .none (.blockOp .equal) [x, y]]
      | some (tagX, xs), some (tagY, ys) =>
        if tagX != tagY || xs.length != ys.length then .list [mkBool false]
        else eqPureList (xs.reverse.zip ys.reverse)
      | some (tag, xs), none =>
        let fields := xs.reverse.zip (List.range xs.length) |>.map fun (e, i) =>
          (e, Exp.op .none (.blockOp (.elemAt i)) [y])
        .append (.list [.op .none (.blockOp (.tagLenEq tag xs.length)) [y]]) (eqPureList fields)
      | none, some (_tag, _ys) => eqPureList [(y, x)]
  | p :: q :: rest => .append (eqPureList [p]) (eqPureList (q :: rest))
termination_by pairs => eqPairsWeight pairs
decreasing_by
  all_goals simp_wf
  · have wx := eqNodeWeight_of_cons x tagX xs _hx
    have wy := eqNodeWeight_of_cons y tagY ys _hy
    have h := eqPairsWeight_zip_le xs.reverse ys.reverse
    simp only [eqNodesWeight_reverse] at h
    simp only [eqPairsWeight, eqPairWeight, Nat.add_zero]
    rw [wx, wy]
    split <;> omega
  · have wx := eqNodeWeight_of_cons x tag xs _hx
    have wy := eqNodeWeight_of_not_cons y _hy
    have h := eqPairsWeight_fields_le xs.reverse y (List.range xs.length)
    simp only [eqNodesWeight_reverse] at h
    simp only [eqPairsWeight, eqPairWeight, Nat.add_zero]
    rw [wx, wy]
    split <;> omega
  · have wx := eqNodeWeight_of_not_cons x _hx
    have wy := eqNodeWeight_of_cons y _tag _ys _hy
    simp only [eqPairsWeight, eqPairWeight, Nat.add_zero]
    rw [wx, wy]
    simp
    split <;> omega
  · simp only [eqPairsWeight, Nat.add_zero]
    have : 0 < eqPairWeight q := by unfold eqPairWeight; split <;> omega
    omega
  · simp only [eqPairsWeight]
    have : 0 < eqPairWeight p := by unfold eqPairWeight; split <;> omega
    omega

/-- Build a short-circuit conjunction with the source empty and singleton cases. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "ConjList_def"]
def conjList : List Exp → Exp
  | [] => mkBool true
  | [x] => x
  | x :: xs => .ifThenElse .none x (conjList xs) (mkBool false)

/-- Decompose a pure equality and join its checks in source order. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_pure_def"]
def eqPure (x y : Exp) : Exp :=
  conjList (appListAppend (eqPureList [(x, y)]))

@[hol "cakeml/compiler/backend/clos_opScript.sml" "is_Var_def"]
def isVar : Exp → Bool
  | .var _ _ => true
  | _ => false

/-- Lift two expressions before constructing a pure equality test. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_any_def"]
def eqAny (x y : Exp) : Option Exp :=
  match liftExpsHOL [x, y] 0 [] with
  | (x :: y :: _, _, binds) => some (.let .none binds (eqPure x y))
  | _ => none

/-- Optimize an equality unless both operands are variables. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_op_def"]
def eqOp (x y : Exp) : Option Exp :=
  if isVar x && isVar y then none else
    match directEq x y with
    | some result => some result
    | none => eqAny x y

/-- The source smart-operation optimization, with failure left explicit. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "SmartOp'_def"]
def smartOp' {α : Type} (_trace : α) (op : Op) (xs : List Exp) : Option Exp :=
  match xs with
  | [x] =>
    match cons x with
    | some (tag, args) => consOp op tag args
    | none => none
  | [x, y] =>
    match destOpConsts x y with
    | some (i, j) => integerOp op i j
    | none =>
      match op with
      | .blockOp .equal => eqOp x y
      | _ => none
  | _ => none

/-- Apply the source smart operation, retaining the original operation on failure. -/
@[hol "cakeml/compiler/backend/clos_opScript.sml" "SmartOp_def"]
def smartOp (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) : Exp :=
  (smartOp' trace op xs).getD (.op trace op xs)

/-- Execute the total source smart operation through the checked interface. -/
def smartFuel (_fuel : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) : Option Exp :=
  some (smartOp trace op xs)

end Flapjack.Compiler.Backend.ClosOp
