import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftCorrect

/-! Simplicity of the source equality decomposition. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang
/-- Invert the constructor case of the simple-expression relation; this is
Flapjack proof infrastructure without a separate HOL declaration. -/
private theorem children (t : BackendCommon.Tra) (tag : Nat) (xs : List Exp)
    (h : SimpleExp (.op t (.blockOp (.cons tag)) xs)) : ∀ x ∈ xs, SimpleExp x := by
  cases h with
  | cons _ _ _ hs => exact hs
/-- Recover simple constructor arguments through the source matcher; this is
Flapjack proof infrastructure without a separate HOL declaration. -/
private theorem consChildren (x : Exp) (tag : Nat) (xs : List Exp)
    (h : cons x = some (tag, xs)) (hs : SimpleExp x) : ∀ e ∈ xs, SimpleExp e := by
  rw [destOpCons_eq_previous] at h
  cases x <;> try simp at h
  case op t op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons tag2 =>
        obtain ⟨rfl,rfl⟩ := h
        exact children _ _ _ hs

/-- Equality decomposition of simple pairs produces simple expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "simple_exp_eq_pure_list"]
theorem eqPureSimple (pairs : List (Exp × Exp))
    (h : ∀ p ∈ pairs, SimpleExp p.1 ∧ SimpleExp p.2) :
    ∀ e ∈ appListAppend (eqPureList pairs), SimpleExp e := by
  fun_induction eqPureList pairs <;> simp_all [appListAppend, appendAux]
  case case2 => exact eqDirectSimpleExp _ _ _ ⟨by assumption, h⟩
  case case3 => exact SimpleExp.equal _ _ _ h.1 h.2
  case case4 => exact SimpleExp.cons _ _ _ (by simp)
  case case5 =>
    rename_i x y hd tagX xs tagY ys hx hy he ih
    apply ih
    intro a b hm
    have hx1 := consChildren x tagY xs hx h.1
    have hy1 := consChildren y tagY ys hy h.2
    exact ⟨hx1 a (List.mem_reverse.mp (List.of_mem_zip hm).1),
      hy1 b (List.mem_reverse.mp (List.of_mem_zip hm).2)⟩
  case case6 =>
    rename_i x y hd tag xs hx hy fields ih
    constructor
    · exact SimpleExp.tagLenEq _ _ _ _ h.2
    · apply ih
      intro a b hm
      simp only [fields, List.mem_map] at hm
      obtain ⟨⟨e,i⟩, hm, heq⟩ := hm
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl,rfl⟩ := heq
      exact ⟨consChildren x tag xs hx h.1 e (List.mem_reverse.mp (List.of_mem_zip hm).1),
        SimpleExp.elemAt _ _ _ h.2⟩
  case case8 =>
    rename_i p q rest ihp ihq
    rw [appendAux_thm]
    intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ihp e hm
    · exact ihq e hm
end Flapjack.Compiler.Backend.ClosOp
