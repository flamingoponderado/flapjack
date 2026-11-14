module

public import Flapjack.Compiler.Backend.ClosOp

@[expose] public section

/-! HOL matcher characterizations and Flapjack preservation facts connecting
the source matchers with the former executable patterns. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- The constructor-operation matcher succeeds exactly on the given tag. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dest_Cons_thm"]
theorem destCons_iff (op : Op) (i : Nat) :
    destCons op = some i ↔ op = .blockOp (.cons i) := by
  cases op <;> try simp [destCons]
  case blockOp b => cases b <;> simp

/-- The constant-operation matcher succeeds on exactly the three literal
constant forms, retaining the original existential witnesses. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dest_Constant_thm"]
theorem destConstant_iff (op : Op) (i : ConstPart) :
    destConstant op = some i ↔ ∃ s w j,
      op = .blockOp (.constant (.constStr s)) ∧ i = .str s ∨
      op = .blockOp (.constant (.constInt j)) ∧ i = .int j ∨
      op = .blockOp (.constant (.constWord64 w)) ∧ i = .w64 w := by
  letI : Nonempty Flapjack.Basis.Pure.MlString.MlString := ⟨Flapjack.Basis.Pure.MlString.ofString ""⟩
  cases op <;> try simp [destConstant]
  case blockOp b =>
    cases b <;> try simp
    case constant c => cases c <;> simp [eq_comm]

/-- The integer-constant matcher succeeds exactly on the given integer. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dest_Const_thm"]
theorem destConst_iff (op : Op) (i : Int) :
    destConst op = some i ↔ op = .intOp (.const i) := by
  cases op <;> try simp [destConst]
  case intOp b => cases b <;> simp

/-- An operation matcher succeeds exactly on a matching operation expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dest_Op_thm"]
theorem destOp_iff {α : Type} (f : Op → Option α) (x : Exp) (i : α) (ys : List Exp) :
    destOp f x = some (i, ys) ↔ ∃ tra op, x = .op tra op ys ∧ f op = some i := by
  cases x <;> try solve | simp [destOp]
  case op tr op args =>
    constructor
    · intro h
      cases hf : f op with
      | none => simp [destOp, hf] at h
      | some v =>
        simp only [destOp, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨tr, op, rfl, hf⟩
    · rintro ⟨tr2, op2, heq, hf⟩
      cases heq
      simp [destOp, hf]

/-- A nullary matcher succeeds exactly on a matching nullary operation. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dest_Op_Nil_thm"]
theorem destOpNil_iff {α : Type} (f : Op → Option α) (x : Exp) (i : α) :
    destOpNil f x = some i ↔ ∃ tra op, x = .op tra op [] ∧ f op = some i := by
  have reduction : destOpNil f x = some i ↔ destOp f x = some (i, []) := by
    unfold destOpNil
    cases h : destOp f x with
    | none => simp
    | some pair =>
      obtain ⟨value, args⟩ := pair
      cases args <;> simp
  exact reduction.trans (destOp_iff f x i [])

/-- Recover an integer literal from the matcher. This Flapjack helper combines
the source operation and integer matcher characterizations. -/
theorem integerLiteral_of_match (x : Exp) (i : Int) (h : destOpNil destConst x = some i) :
    ∃ trace, x = .op trace (.intOp (.const i)) [] := by
  obtain ⟨trace, op, eq, found⟩ := (destOpNil_iff destConst x i).1 h
  have opEq := (destConst_iff op i).1 found
  exact ⟨trace, by simpa [opEq] using eq⟩

/-- The source integer-expression matcher preserves the former pattern. -/
theorem destOpConst_eq_previous (e : Exp) :
    destOpNil destConst e = match e with
      | .op _ (.intOp (.const i)) [] => some i
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case intOp i => cases i <;> cases xs <;> rfl

/-- The source constructor-expression matcher preserves the former pattern. -/
theorem destOpCons_eq_previous (e : Exp) :
    cons e = match e with
      | .op _ (.blockOp (.cons tag)) xs => some (tag, xs)
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case blockOp op => cases op <;> rfl

/-- The source nullary-constructor matcher preserves the former pattern. -/
theorem destOpConsNil_eq_previous (e : Exp) :
    destOpNil destCons e = match e with
      | .op _ (.blockOp (.cons tag)) [] => some tag
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case blockOp op => cases op <;> cases xs <;> rfl

/-- The source constant-expression matcher preserves the former pattern. -/
theorem destOpConstant_eq_previous (e : Exp) :
    destOpNil destConstant e = match e with
      | .op _ (.blockOp (.constant (.constInt i))) [] => some (.int i)
      | .op _ (.blockOp (.constant (.constStr s))) [] => some (.str s)
      | .op _ (.blockOp (.constant (.constWord64 w))) [] => some (.w64 w)
      | _ => none := by
  cases e <;> try rfl
  case op t op xs =>
    cases op <;> try rfl
    case blockOp op =>
      cases op <;> try rfl
      case constant value => cases value <;> cases xs <;> rfl

end Flapjack.Compiler.Backend.ClosOp
