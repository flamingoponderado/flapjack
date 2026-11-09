module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftReduction

@[expose] public section

/-! Direct-equality reduction correspondence. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem dontRed (x : Exp) (h : dontLift x = true) : RedRel [x] [] := by
  apply simpleExpRedRel
  simp only [List.mem_singleton, forall_eq]
  rcases (dontLiftCharacterization x).mp h with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩
  · exact .intConst _ _
  · exact .cons _ _ _ (by simp)
  · exact .constStr _ _
  · exact .constInt _ _
  · exact .constWord64 _ _

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem isInt (x : Exp) (i : Int) (h : destOpNil destConst x = some i) : dontLift x = true := by
  change ((destOpNil destConst x).isSome || (destOpNil destCons x).isSome ||
    (destOpNil destConstant x).isSome) = true
  simp [h]
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem isNil (x : Exp) (i : Nat) (h : destOpNil destCons x = some i) : dontLift x = true := by
  change ((destOpNil destConst x).isSome || (destOpNil destCons x).isSome ||
    (destOpNil destConstant x).isSome) = true
  simp [h]
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem isConst (x : Exp) (i : ConstPart) (h : destOpNil destConstant x = some i) : dontLift x = true := by
  change ((destOpNil destConst x).isSome || (destOpNil destCons x).isSome ||
    (destOpNil destConstant x).isSome) = true
  simp [h]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem pairL (x y : Exp) (hx : RedRel [x] []) : RedRel [x,y] [y] := by
  simpa using RedRel.multi x y [] [] [y] hx (.refl y)
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem pairR (x y : Exp) (hy : RedRel [y] []) : RedRel [x,y] [x] := by
  simpa using RedRel.multi x y [] [x] [] (.refl x) hy
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem pairBoth (x y : Exp) (hx : RedRel [x] []) (hy : RedRel [y] []) : RedRel [x,y] [] := by
  simpa using RedRel.multi x y [] [] [] hx hy
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem boolRed (b : Bool) : RedRel [mkBool b] [] := by
  cases b with
  | false => exact .op 0 [] [] .none _ (.const 0) 0 0 0 0 (.implode []) 0 .nil (by simp)
  | true => exact .op 0 [] [] .none _ (.const 0) 0 1 0 0 (.implode []) 0 .nil (by simp)
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intEqRed (i : Int) (x : Exp) : RedRel [.op .none (.blockOp (.equalConst (.int i))) [x]] [x] := by
  exact .op 0 [x] [x] .none _ (.const 0) i 0 0 0 (.implode []) 0 (.refl x) (by simp)
/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem tagRed (i : Nat) (x : Exp) : RedRel [.op .none (.blockOp (.tagLenEq i 0)) [x]] [x] := by
  exact .op 0 [x] [x] .none _ (.const 0) 0 0 i 0 (.implode []) 0 (.refl x) (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intStage (x y z : Exp) (h : eqDirectConst x y = some z) :
    ∃ ys, RedRel [x,y] ys ∧ RedRel [z] ys := by
  unfold eqDirectConst at h
  split at h <;> simp_all
  all_goals subst z
  all_goals first
    | exact ⟨[], pairBoth x y (dontRed x (isInt x _ (by assumption))) (dontRed y (isInt y _ (by assumption))), boolRed _⟩
    | exact ⟨[y], pairL x y (dontRed x (isInt x _ (by assumption))), intEqRed _ y⟩
    | exact ⟨[x], pairR x y (dontRed y (isInt y _ (by assumption))), intEqRed _ x⟩

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem constEqRed (p : ConstPart) (source x : Exp)
    (h : destOpNil destConstant source = some p) :
    RedRel [.op .none (.blockOp (.equalConst p)) [x]] [x] := by
  cases p with
  | con tag xs =>
    rw [destOpConstant_eq_previous] at h
    cases source <;> try simp at h
    case op t op args =>
      cases op <;> try simp at h
      case blockOp op =>
        cases op <;> try simp at h
        case constant v => cases v <;> cases args <;> simp at h
  | int i => exact .op 0 [x] [x] .none _ (.const 0) i 0 0 0 (.implode []) 0 (.refl x) (by simp)
  | str s => exact .op 0 [x] [x] .none _ (.const 0) 0 0 0 0 s 0 (.refl x) (by simp)
  | w64 w => exact .op 0 [x] [x] .none _ (.const 0) 0 0 0 0 (.implode []) w (.refl x) (by simp)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem constantStage (x y z : Exp) (h : eqDirectConstant x y = some z) :
    ∃ ys, RedRel [x,y] ys ∧ RedRel [z] ys := by
  unfold eqDirectConstant at h
  split at h <;> simp_all
  all_goals subst z
  all_goals first
    | exact ⟨[], pairBoth x y (dontRed x (isConst x _ (by assumption))) (dontRed y (isConst y _ (by assumption))), boolRed _⟩
    | exact ⟨[y], pairL x y (dontRed x (isConst x _ (by assumption))), constEqRed _ x y (by assumption)⟩
    | exact ⟨[x], pairR x y (dontRed y (isConst y _ (by assumption))), constEqRed _ y x (by assumption)⟩

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem nilStage (x y z : Exp) (h : eqDirectNil x y = some z) :
    ∃ ys, RedRel [x,y] ys ∧ RedRel [z] ys := by
  unfold eqDirectNil at h
  split at h <;> simp_all
  all_goals subst z
  all_goals first
    | exact ⟨[], pairBoth x y (dontRed x (isNil x _ (by assumption))) (dontRed y (isNil y _ (by assumption))), boolRed _⟩
    | exact ⟨[y], pairL x y (dontRed x (isNil x _ (by assumption))), tagRed _ y⟩
    | exact ⟨[x], pairR x y (dontRed y (isNil y _ (by assumption))), tagRed _ x⟩

/-- Source direct equality produces the same residual as its two operands. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_red_rel"]
theorem directRed (x y z : Exp) (h : directEq x y = some z) :
    ∃ ys, RedRel [x,y] ys ∧ RedRel [z] ys := by
  cases hc : eqDirectConst x y with
  | some e => simp [directEq, hc] at h; subst z; exact intStage x y e hc
  | none =>
    cases hd : eqDirectConstant x y with
    | some e => simp [directEq, hc, hd] at h; subst z; exact constantStage x y e hd
    | none =>
      simp [directEq, hc, hd] at h
      exact nilStage x y z h
/-- Any expression list reduces to itself. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_refl"]
theorem redRelRefl (xs : List Exp) : RedRel xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact redRelConsOne xs xs x ih

/-- Reduction preservation for the lifted-equality branch. This is a
Flapjack proof helper, not a separate HOL declaration. -/
theorem eqAnyRed (x y z : Exp) (h : eqAny x y = some z) :
    ∃ ys, RedRel [x,y] ys ∧ RedRel [z] ys := by
  generalize heq : liftExpsHOL [x,y] 0 [] = result
  obtain ⟨lifted,n,binds⟩ := result
  have hr := liftExpsRedRel [x,y] 0 [] lifted n binds heq
  have hs := liftExpsSimpleExp [x,y] 0 [] lifted n binds heq
  cases lifted with
  | nil => simp [eqAny, heq] at h
  | cons a rest =>
    cases rest with
    | nil => simp [eqAny, heq] at h
    | cons b rest =>
      simp [eqAny, heq] at h
      subst z
      obtain ⟨ys, hxy, hb⟩ := hr
      have ha : SimpleExp a := hs a (by simp)
      have hc : SimpleExp b := hs b (by simp)
      refine ⟨ys,hxy,?_⟩
      apply RedRel.letE binds (eqPure a b) ys .none
      · simpa using hb
      · exact redRelEqPure a b ⟨ha,hc⟩

/-- Reduction preservation for successful equality optimization. This is a
Flapjack proof helper, not a separate HOL declaration. -/
theorem eqOpRed (x y z : Exp) (h : eqOp x y = some z) :
    ∃ ys, RedRel [x,y] ys ∧ RedRel [z] ys := by
  unfold eqOp at h
  split at h
  · contradiction
  · cases hd : directEq x y with
    | none => simp only [hd] at h; exact eqAnyRed x y z h
    | some value =>
      simp only [hd, Option.some.injEq] at h
      subst z
      exact directRed x y value hd

end Flapjack.Compiler.Backend.ClosOp
