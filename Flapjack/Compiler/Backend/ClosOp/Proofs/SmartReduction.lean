import Flapjack.Compiler.Backend.ClosOp.Proofs.EqDirectReduction

/-! Source smart-operation reduction correctness. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intRed (i : Int) : RedRel [mkInt i] [] :=
  .op 0 [] [] .none _ (.const i) 0 0 0 0 (.implode []) 0 .nil (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem boolRed (b : Bool) : RedRel [mkBool b] [] := by
  cases b with
  | false => exact .op 0 [] [] .none _ (.const 0) 0 0 0 0 (.implode []) 0 .nil (by simp)
  | true => exact .op 0 [] [] .none _ (.const 0) 0 1 0 0 (.implode []) 0 .nil (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intMatchRed (x : Exp) (i : Int) (h : destOpNil destConst x = some i) : RedRel [x] [] := by
  rw [destOpConst_eq_previous] at h
  cases x <;> try simp at h
  case op t op args =>
    cases op <;> try simp at h
    case intOp op =>
      cases op <;> try simp at h
      case const i' =>
        cases args <;> simp_all
        exact .op 0 [] [] t _ (.const i) 0 0 0 0 (.implode []) 0 .nil (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intRoot (t : BackendCommon.Tra) (op : IntOp) (xs : List Exp)
    (h : RedRel xs []) : RedRel [.op t (.intOp op) xs] [] :=
  .op 0 xs [] t _ op 0 0 0 0 (.implode []) 0 h (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem equalRoot (t : BackendCommon.Tra) (xs : List Exp) (ys : List Exp)
    (h : RedRel xs ys) : RedRel [.op t (.blockOp .equal) xs] ys :=
  .op 0 xs ys t _ (.const 0) 0 0 0 0 (.implode []) 0 h (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem integerStage (t : BackendCommon.Tra) (op : Op) (x y z : Exp) (i j : Int)
    (hc : destOpConsts x y = some (i,j)) (h : integerOp op i j = some z) :
    ∃ ys, RedRel [.op t op [x,y]] ys ∧ RedRel [z] ys := by
  unfold destOpConsts at hc
  cases hx : destOpNil destConst x <;> cases hy : destOpNil destConst y <;> simp_all
  have hp : RedRel [x,y] [] := by
    simpa using RedRel.multi x y [] [] [] (intMatchRed x i hx) (intMatchRed y j hy)
  cases op <;> try simp [integerOp] at h
  case intOp io =>
    cases io <;> simp at h
    all_goals subst z
    all_goals first | exact ⟨[], intRoot t _ [x,y] hp, intRed _⟩ | exact ⟨[], intRoot t _ [x,y] hp, boolRed _⟩
  case blockOp bo =>
    cases bo <;> simp at h
    subst z
    exact ⟨[], equalRoot t [x,y] [] hp, boolRed _⟩

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem consStage (t : BackendCommon.Tra) (op : Op) (x z : Exp)
    (tag : Nat) (args : List Exp) (hc : cons x = some (tag,args))
    (h : consOp op tag args = some z) :
    ∃ ys, RedRel [.op t op [x]] ys ∧ RedRel [z] ys := by
  rw [destOpCons_eq_previous] at hc
  cases x <;> try simp at hc
  case op tx ox xs =>
    cases ox <;> try simp at hc
    case blockOp ox =>
      cases ox <;> try simp at hc
      case cons tagx =>
        obtain ⟨rfl,rfl⟩ := hc
        have hi : RedRel [.op tx (.blockOp (.cons tagx)) xs] xs :=
          .op 0 xs xs tx _ (.const 0) 0 tagx 0 0 (.implode []) 0 (redRelRefl xs) (by simp)
        cases op <;> try simp [consOp, destElemAt, destTagLenEq, destTagEq, destLenEq] at h
        case blockOp b =>
          cases b <;> simp at h
          case elemAt n =>
            obtain ⟨_,rfl⟩ := h
            refine ⟨xs, .op 0 _ xs t _ (.const 0) 0 0 n 0 (.implode []) 0 hi (by simp), ?_⟩
            exact .letE xs _ xs .none (redRelRefl xs) (.var _ .none)
          case tagLenEq n len =>
            subst z
            refine ⟨xs, .op 0 _ xs t _ (.const 0) 0 0 n len (.implode []) 0 hi (by simp), ?_⟩
            exact .letE xs _ xs .none (redRelRefl xs) (boolRed _)
          case lenEq len =>
            subst z
            refine ⟨xs, .op len _ xs t _ (.const 0) 0 0 0 0 (.implode []) 0 hi (by simp), ?_⟩
            exact .letE xs _ xs .none (redRelRefl xs) (boolRed _)
          case tagEq n =>
            subst z
            refine ⟨xs, .op 0 _ xs t _ (.const 0) 0 n 0 0 (.implode []) 0 hi (by simp), ?_⟩
            exact .letE xs _ xs .none (redRelRefl xs) (boolRed _)

/-- The source smart operation preserves a common reduction residual. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_exists"]
theorem smartRed (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    ∃ ys, RedRel [.op t op xs] ys ∧ RedRel [smartOp t op xs] ys := by
  cases hs : smartOp' t op xs with
  | none =>
    refine ⟨[.op t op xs], .refl _, ?_⟩
    simpa [smartOp, hs] using (RedRel.refl (.op t op xs))
  | some z =>
    have hz : smartOp t op xs = z := by simp [smartOp, hs]
    rw [hz]
    cases xs with
    | nil => simp [smartOp'] at hs
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [smartOp'] at hs
        cases hc : cons x with
        | none => simp [hc] at hs
        | some p =>
          obtain ⟨tag,args⟩ := p
          simp only [hc] at hs
          exact consStage t op x z tag args hc hs
      | cons y rest =>
        cases rest with
        | cons third rest => simp [smartOp'] at hs
        | nil =>
          simp only [smartOp'] at hs
          cases hc : destOpConsts x y with
          | some p =>
            obtain ⟨i,j⟩ := p
            simp only [hc] at hs
            exact integerStage t op x y z i j hc hs
          | none =>
            simp only [hc] at hs
            cases op <;> try simp at hs
            case blockOp b =>
              cases b <;> try simp at hs
              case equal =>
                obtain ⟨ys, hxy, hz⟩ := eqOpRed x y z hs
                exact ⟨ys, equalRoot t [x,y] ys hxy, hz⟩
end Flapjack.Compiler.Backend.ClosOp
