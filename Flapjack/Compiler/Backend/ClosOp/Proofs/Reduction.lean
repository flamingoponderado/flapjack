module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.EqPureSimple

@[expose] public section

/-! Source reduction relation and its simple-expression consequences. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang Flapjack.Basis.Pure.MlString

/-- The source relation records the expressions remaining after reductions. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel"]
inductive RedRel : List Exp → List Exp → Prop where
  | op (n : Nat) (xs ys : List Exp) (t : BackendCommon.Tra) (op : Op)
      (iop : IntOp) (i : Int) (tag t1 t2 : Nat) (s : MlString) (w : BitVec 64) :
      RedRel xs ys → op ∈ [
        .intOp iop, .blockOp .equal, .blockOp (.cons tag), .blockOp (.elemAt t1),
        .blockOp (.tagLenEq t1 t2), .blockOp (.lenEq n), .blockOp (.tagEq tag),
        .blockOp (.equalConst (.str s)), .blockOp (.equalConst (.w64 w)),
        .blockOp (.equalConst (.int i)), .blockOp (.constant (.constInt i)),
        .blockOp (.constant (.constStr s)), .blockOp (.constant (.constWord64 w))] →
      RedRel [.op t op xs] ys
  | nil : RedRel [] []
  | refl (x : Exp) : RedRel [x] [x]
  | var (v : Nat) (t : BackendCommon.Tra) : RedRel [.var t v] []
  | multi (x y : Exp) (zs x1 x2 : List Exp) :
      RedRel [x] x1 → RedRel (y :: zs) x2 → RedRel (x :: y :: zs) (x1 ++ x2)
  | letE (xs : List Exp) (x : Exp) (x1 : List Exp) (t : BackendCommon.Tra) :
      RedRel xs x1 → RedRel [x] [] → RedRel [.let t xs x] x1
  | ite (t : BackendCommon.Tra) (x y z : Exp) (x1 x2 x3 : List Exp) :
      RedRel [x] x1 → RedRel [y] x2 → RedRel [z] x3 →
      RedRel [.ifThenElse t x y z] (x1 ++ x2 ++ x3)

/-- The empty input can reduce only to the empty output. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_nil"]
theorem redRelNil (ys : List Exp) : RedRel [] ys ↔ ys = [] := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst ys; exact .nil

/-- Individually reducible expressions reduce together to the empty list. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_EVERY"]
theorem redRelEvery (xs : List Exp) (h : ∀ e ∈ xs, RedRel [e] []) : RedRel xs [] := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases xs with
    | nil => exact h x (by simp)
    | cons y zs =>
      have hx := h x (by simp)
      have ht := ih (fun e he => h e (by simp [he]))
      simpa using RedRel.multi x y zs [] [] hx ht

/-- Each simple expression reduces to no residual expressions. This helper
is Flapjack proof infrastructure without a separate HOL declaration. -/
private theorem simpleSingle (x : Exp) (h : SimpleExp x) : RedRel [x] [] := by
  induction h with
  | var t i => exact .var i t
  | ite t x y z hx hy hz ihx ihy ihz =>
    simpa using RedRel.ite t x y z [] [] [] ihx ihy ihz
  | intConst t i =>
    exact .op 0 [] [] t _ (.const i) 0 0 0 0 (.implode []) 0 .nil (by simp)
  | constInt t i =>
    exact .op 0 [] [] t _ (.const 0) i 0 0 0 (.implode []) 0 .nil (by simp)
  | constStr t s =>
    exact .op 0 [] [] t _ (.const 0) 0 0 0 0 s 0 .nil (by simp)
  | constWord64 t w =>
    exact .op 0 [] [] t _ (.const 0) 0 0 0 0 (.implode []) w .nil (by simp)
  | cons t i xs hs ih =>
    exact .op 0 xs [] t _ (.const 0) 0 i 0 0 (.implode []) 0 (redRelEvery xs ih) (by simp)
  | equalInt t i x hx ih =>
    exact .op 0 [x] [] t _ (.const 0) i 0 0 0 (.implode []) 0 ih (by simp)
  | equalStr t s x hx ih =>
    exact .op 0 [x] [] t _ (.const 0) 0 0 0 0 s 0 ih (by simp)
  | equalWord64 t w x hx ih =>
    exact .op 0 [x] [] t _ (.const 0) 0 0 0 0 (.implode []) w ih (by simp)
  | elemAt t i x hx ih =>
    exact .op 0 [x] [] t _ (.const 0) 0 0 i 0 (.implode []) 0 ih (by simp)
  | equal t x y hx hy ihx ihy =>
    have hxy : RedRel [x,y] [] := by simpa using RedRel.multi x y [] [] [] ihx ihy
    exact .op 0 [x,y] [] t _ (.const 0) 0 0 0 0 (.implode []) 0 hxy (by simp)
  | tagLenEq t tag len x hx ih =>
    exact .op 0 [x] [] t _ (.const 0) 0 0 tag len (.implode []) 0 ih (by simp)

/-- Every list of simple expressions reduces to the empty list. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "simple_exp_red_rel"]
theorem simpleExpRedRel (xs : List Exp) (h : ∀ e ∈ xs, SimpleExp e) : RedRel xs [] := by
  apply redRelEvery
  intro e he
  exact simpleSingle e (h e he)

/-- Split a non-singleton empty reduction into its two source premises. This
is Flapjack proof infrastructure without a separate HOL declaration. -/
private theorem splitOutput (x y : Exp) (zs out : List Exp) (h : RedRel (x :: y :: zs) out) :
    ∃ a b, out = a ++ b ∧ RedRel [x] a ∧ RedRel (y :: zs) b := by
  cases h with
  | multi x y zs x1 x2 hx hy =>
    exact ⟨x1, x2, rfl, hx, hy⟩

private theorem splitEmpty (x y : Exp) (zs : List Exp) (h : RedRel (x :: y :: zs) []) :
    RedRel [x] [] ∧ RedRel (y :: zs) [] := by
  obtain ⟨a,b,heq,ha,hb⟩ := splitOutput x y zs [] h
  have hnil := List.append_eq_nil_iff.mp heq.symm
  simpa [hnil.1, hnil.2] using And.intro ha hb

/-- A conjunction of expressions reducing to empty also reduces to empty. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_ConjList"]
theorem redRelConjList (xs : List Exp) (h : RedRel xs []) : RedRel [conjList xs] [] := by
  induction xs with
  | nil =>
    exact .op 0 [] [] .none _ (.const 0) 0 1 0 0 (.implode []) 0 .nil (by simp)
  | cons x xs ih =>
    cases xs with
    | nil => exact h
    | cons y zs =>
      obtain ⟨hx, ht⟩ := splitEmpty x y zs h
      have hf : RedRel [mkBool false] [] :=
        .op 0 [] [] .none _ (.const 0) 0 0 0 0 (.implode []) 0 .nil (by simp)
      simpa [conjList] using RedRel.ite .none x (conjList (y :: zs)) (mkBool false) [] [] [] hx (ih ht) hf

/-- Pure equality of simple inputs reduces to the empty residual list. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_eq_pure"]
theorem redRelEqPure (x y : Exp) (h : SimpleExp x ∧ SimpleExp y) : RedRel [eqPure x y] [] := by
  apply redRelConjList
  apply simpleExpRedRel
  apply eqPureSimple
  simpa using h

/-- Reduction of a nonempty list splits into a head and tail reduction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "red_rel_exists_append"]
theorem redRelExistsAppend (head : Exp) (xs ys : List Exp) :
    RedRel (head :: xs) ys ↔
      ∃ ys1 ys2, RedRel [head] ys1 ∧ RedRel xs ys2 ∧ ys = ys1 ++ ys2 := by
  constructor
  · intro h
    cases xs with
    | nil => exact ⟨ys, [], h, .nil, by simp⟩
    | cons y zs =>
      obtain ⟨a,b,heq,ha,hb⟩ := splitOutput head y zs ys h
      exact ⟨a,b,ha,hb,heq⟩
  · rintro ⟨a,b,ha,hb,rfl⟩
    cases xs with
    | nil =>
      have hb0 := (redRelNil b).mp hb
      simpa [hb0] using ha
    | cons y zs => exact .multi head y zs a b ha hb

/-- A head reduction and tail reduction concatenate their residuals. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "IMP_red_rel_cons_0"]
theorem redRelConsZero (x : Exp) (ys xs zs : List Exp)
    (h : RedRel [x] ys ∧ RedRel xs zs) : RedRel (x :: xs) (ys ++ zs) := by
  exact (redRelExistsAppend x xs (ys ++ zs)).mpr ⟨ys,zs,h.1,h.2,rfl⟩

/-- Concatenating two reductions concatenates their residuals. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "IMP_red_rel_append"]
theorem redRelAppend (xs ys xs1 ys1 : List Exp)
    (h : RedRel xs ys ∧ RedRel xs1 ys1) : RedRel (xs ++ xs1) (ys ++ ys1) := by
  induction xs generalizing ys with
  | nil =>
    have hy := (redRelNil ys).mp h.1
    simpa [hy] using h.2
  | cons x xs ih =>
    obtain ⟨a,b,ha,hb,hy⟩ := (redRelExistsAppend x xs ys).mp h.1
    subst ys
    have ht := ih b ⟨hb,h.2⟩
    simpa [List.append_assoc] using redRelConsZero x a (xs ++ xs1) (b ++ ys1) ⟨ha,ht⟩

/-- A head with no residuals can be prepended to any reduction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "IMP_red_rel_cons"]
theorem redRelCons (x : Exp) (xs ys : List Exp)
    (h : RedRel [x] [] ∧ RedRel xs ys) : RedRel (x :: xs) ys := by
  simpa using redRelConsZero x [] xs ys h

/-- Preserve an arbitrary leading expression in the residual list. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "IMP_red_rel_cons_1"]
theorem redRelConsOne (xs ys : List Exp) (x : Exp) (h : RedRel xs ys) :
    RedRel (x :: xs) (x :: ys) := by
  simpa using redRelConsZero x [x] xs ys ⟨.refl x,h⟩

end Flapjack.Compiler.Backend.ClosOp
