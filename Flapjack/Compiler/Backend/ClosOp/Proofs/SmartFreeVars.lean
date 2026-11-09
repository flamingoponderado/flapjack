module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftFreeVars

@[expose] public section

/-! Free-variable preservation for the source smart operation. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosProps

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem fvMember (n : Nat) (xs : List Exp) :
    freeVars n xs ↔ ∃ e ∈ xs, freeVarExp n e := by
  induction xs with
  | nil => simp [freeVars]
  | cons x xs ih => simp [freeVars, ih, or_and_right, exists_or]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem fvAppend (n : Nat) (xs ys : List Exp) :
    freeVars n (xs ++ ys) ↔ freeVars n xs ∨ freeVars n ys := by
  induction xs with
  | nil => simp [freeVars]
  | cons x xs ih => simp [freeVars, ih, or_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem consFV (x : Exp) (tag : Nat) (ys : List Exp)
    (h : cons x = some (tag,ys)) (l : Nat) : freeVarExp l x ↔ freeVars l ys := by
  rw [destOpCons_eq_previous] at h
  cases x <;> try simp at h
  case op t op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons tag2 => obtain ⟨rfl,rfl⟩ := h; rfl

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intStageFV (x y z : Exp) (h : eqDirectConst x y = some z) (n : Nat)
    (fv : freeVarExp n z) : freeVarExp n x ∨ freeVarExp n y := by
  unfold eqDirectConst at h
  split at h <;> simp_all
  all_goals subst z
  all_goals try simp_all [freeVarExp, freeVars, mkBool]
  all_goals first
    | change freeVarExp n (.op .none (.blockOp (.equalConst _)) [y]) at fv; exact Or.inr (by simpa [freeVarExp, freeVars] using fv)
    | change freeVarExp n (.op .none (.blockOp (.equalConst _)) [x]) at fv; exact Or.inl (by simpa [freeVarExp, freeVars] using fv)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem constStageFV (x y z : Exp) (h : eqDirectConstant x y = some z) (n : Nat)
    (fv : freeVarExp n z) : freeVarExp n x ∨ freeVarExp n y := by
  unfold eqDirectConstant at h
  split at h <;> simp_all
  all_goals subst z
  all_goals try simp_all [freeVarExp, freeVars, mkBool]
  all_goals first
    | change freeVarExp n (.op .none (.blockOp (.equalConst _)) [y]) at fv; exact Or.inr (by simpa [freeVarExp, freeVars] using fv)
    | change freeVarExp n (.op .none (.blockOp (.equalConst _)) [x]) at fv; exact Or.inl (by simpa [freeVarExp, freeVars] using fv)

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem nilStageFV (x y z : Exp) (h : eqDirectNil x y = some z) (n : Nat)
    (fv : freeVarExp n z) : freeVarExp n x ∨ freeVarExp n y := by
  unfold eqDirectNil at h
  split at h <;> simp_all
  all_goals subst z
  all_goals simp_all [freeVarExp, freeVars, mkBool]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem directFV (x y z : Exp) (h : directEq x y = some z) (n : Nat)
    (fv : freeVarExp n z) : freeVarExp n x ∨ freeVarExp n y := by
  cases hc : eqDirectConst x y with
  | some e => simp [directEq, hc] at h; subst z; exact intStageFV x y e hc n fv
  | none =>
    cases hd : eqDirectConstant x y with
    | some e => simp [directEq, hc, hd] at h; subst z; exact constStageFV x y e hd n fv
    | none => simp [directEq, hc, hd] at h; exact nilStageFV x y z h n fv

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem treeFV (pairs : List (Exp × Exp)) (n : Nat)
    (h : freeVars n (appListAppend (eqPureList pairs))) :
    ∃ p ∈ pairs, freeVarExp n p.1 ∨ freeVarExp n p.2 := by
  revert h
  fun_induction eqPureList pairs <;> simp_all [appListAppend, appendAux, freeVars, freeVarExp]
  case case2 => intro hv; exact directFV _ _ _ (by assumption) n hv
  case case4 => simp [mkBool, freeVarExp, freeVars]
  case case5 =>
    rename_i x y hd tagX xs tagY ys hx hy he ih
    intro hv
    obtain ⟨a,b,hm,hv⟩ := ih hv
    rcases hv with hv | hv
    · apply Or.inl
      apply (consFV x tagY xs hx n).mpr
      exact (fvMember n xs).mpr ⟨a,List.mem_reverse.mp (List.of_mem_zip hm).1,hv⟩
    · apply Or.inr
      apply (consFV y tagY ys hy n).mpr
      exact (fvMember n ys).mpr ⟨b,List.mem_reverse.mp (List.of_mem_zip hm).2,hv⟩
  case case6 =>
    rename_i x y hd tag xs hx hy fields ih
    intro hv
    rcases hv with hv | hv
    · exact Or.inr hv
    · obtain ⟨a,b,hm,hv⟩ := ih hv
      simp only [fields, List.mem_map] at hm
      obtain ⟨⟨e,i⟩, hm, heq⟩ := hm
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl,rfl⟩ := heq
      simp only [freeVarExp, freeVars, or_false] at hv
      rcases hv with hv | hv
      · exact Or.inl ((consFV x tag xs hx n).mpr ((fvMember n xs).mpr ⟨e,List.mem_reverse.mp (List.of_mem_zip hm).1,hv⟩))
      · exact Or.inr hv
  case case7 =>
    rename_i x y hd tag ys hx hy ih
    intro hv
    exact Or.symm (ih hv)
  case case8 =>
    rename_i p q rest ihp ihrest
    intro hv
    rw [appendAux_thm, fvAppend] at hv
    rcases hv with hv | hv
    · exact Or.inl (ihp hv)
    · exact Or.inr (ihrest hv)

/-- Pure equality introduces no free variables outside its two inputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "fv1_eq_pure"]
theorem eqPureFV (n : Nat) (x y : Exp) (h : freeVar n (eqPure x y)) :
    freeVar n x ∨ freeVar n y := by
  have hf : freeVars n (appListAppend (eqPureList [(x,y)])) :=
    (freeVarConjList n _).mp h
  obtain ⟨p,hp,hv⟩ := treeFV [(x,y)] n hf
  simp only [List.mem_singleton] at hp
  subst p
  simpa [freeVar, freeVars] using hv

/-- Successful equality optimization introduces no free variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_op_fv"]
theorem eqOpFV (x y z : Exp) (n : Nat) (h : eqOp x y = some z)
    (fv : freeVars n [z]) : freeVars n [x] ∨ freeVars n [y] := by
  unfold eqOp at h
  split at h
  · contradiction
  · cases hd : directEq x y with
    | some e =>
      simp only [hd, Option.some.injEq] at h
      subst z
      have hv : freeVarExp n e := by simpa [freeVars] using fv
      simpa [freeVars] using directFV x y e hd n hv
    | none =>
      simp only [hd] at h
      generalize heq : liftExpsHOL [x,y] 0 [] = result
      obtain ⟨lifted,k,binds⟩ := result
      have hl := liftExpsFV [x,y] 0 [] lifted k binds ⟨heq,rfl⟩
      cases lifted with
      | nil => simp [eqAny, heq] at h
      | cons a rest =>
        cases rest with
        | nil => simp [eqAny, heq] at h
        | cons b rest =>
          simp [eqAny, heq] at h
          subst z
          simp only [freeVars, freeVarExp, or_false] at fv
          rcases fv with hv | hv
          · have ho := hl.2.1 n hv
            simpa [freeVars, or_assoc] using ho
          · have hp : freeVar (n + binds.length) (eqPure a b) := by simpa [freeVar,freeVars] using hv
            rcases eqPureFV (n + binds.length) a b hp with ha | hb
            · have hf : freeVars (n + binds.length) (a :: b :: rest) := by
                simp only [freeVars]; exact Or.inl (by simpa [freeVar,freeVars] using ha)
              have bound := hl.2.2 _ hf
              omega
            · have hf : freeVars (n + binds.length) (a :: b :: rest) := by
                simp only [freeVars]; exact Or.inr (Or.inl (by simpa [freeVar,freeVars] using hb))
              have bound := hl.2.2 _ hf
              omega

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem integerFV (op : Op) (i j : Int) (z : Exp) (h : integerOp op i j = some z)
    (n : Nat) : ¬ freeVarExp n z := by
  cases op <;> try simp [integerOp] at h
  case intOp io =>
    cases io <;> simp at h
    all_goals subst z
    all_goals simp [freeVarExp,freeVars,mkBool,mkInt]
  case blockOp bo =>
    cases bo <;> simp at h
    subst z
    simp [freeVarExp,freeVars,mkBool]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem consStageFV (op : Op) (tag : Nat) (args : List Exp) (z : Exp)
    (h : consOp op tag args = some z) (n : Nat) (hv : freeVarExp n z) : freeVars n args := by
  cases op <;> try simp [consOp,destElemAt,destTagLenEq,destTagEq,destLenEq] at h
  case blockOp b =>
    cases b <;> simp at h
    case elemAt i =>
      obtain ⟨hi,rfl⟩ := h
      simp only [freeVarExp] at hv
      rcases hv with hv | hv
      · exact hv
      · omega
    all_goals subst z
    all_goals simpa [freeVarExp,freeVars,mkBool] using hv

/-- Smart operations introduce no free variables outside the original operation. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "fv1_SmartOp"]
theorem smartFV (n : Nat) (t : BackendCommon.Tra) (op : Op) (xs : List Exp)
    (h : freeVar n (smartOp t op xs)) : freeVar n (.op t op xs) := by
  cases hs : smartOp' t op xs with
  | none => simpa [smartOp,hs] using h
  | some z =>
    have hz : smartOp t op xs = z := by simp [smartOp,hs]
    rw [hz] at h
    have hzfv : freeVarExp n z := by simpa [freeVar,freeVars] using h
    have target : freeVars n xs := by
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
            have hv := consStageFV op tag args z hs n hzfv
            have hx := (consFV x tag args hc n).mpr hv
            simpa [freeVars] using hx
        | cons y rest =>
          cases rest with
          | cons third rest => simp [smartOp'] at hs
          | nil =>
            simp only [smartOp'] at hs
            cases hc : destOpConsts x y with
            | some p =>
              obtain ⟨i,j⟩ := p
              simp only [hc] at hs
              exact False.elim (integerFV op i j z hs n hzfv)
            | none =>
              simp only [hc] at hs
              cases op <;> try simp at hs
              case blockOp b =>
                cases b <;> try simp at hs
                case equal =>
                  have hv : freeVars n [z] := by simpa [freeVars] using hzfv
                  have he := eqOpFV x y z n hs hv
                  simpa [freeVars] using he
    simpa [freeVar,freeVars,freeVarExp] using target
end Flapjack.Compiler.Backend.ClosOp
