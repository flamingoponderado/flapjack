module

public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosLang.Pure

@[expose] public section

/-! Purity preservation by the direct-call pass. -/

namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

mutual
/-- Mutual traversal induction for the purity preservation proof. -/
private theorem pureSing (e : Exp) (s : State) (h : pure e = true) :
    pure (callsSing e s).1 = true := by
  cases e <;> simp only [ClosLang.pure, Bool.and_eq_true, Bool.false_eq_true] at h ⊢
  all_goals simp only [callsSing, ClosLang.pure]
  case ifThenElse t x y z =>
    simp only [Bool.and_eq_true]
    exact ⟨⟨pureSing x s h.1.1, pureSing y _ h.1.2⟩, pureSing z _ h.2⟩
  case «let» t xs body =>
    simp only [Bool.and_eq_true]
    exact ⟨pureSingList xs s h.1, pureSing body _ h.2⟩
  case handle t body handler => exact pureSing body s h
  case fn => split <;> rfl
  case letrec names loc ws fns body =>
    split <;> simp only [ClosLang.pure] <;> exact pureSing body _ h
  case op t op xs =>
    simp only [Bool.and_eq_true]
    exact ⟨pureSingList xs s h.1, h.2⟩
termination_by sizeOf e
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- List half of the traversal induction. -/
private theorem pureSingList (es : List Exp) (s : State) (h : pureList es = true) :
    pureList (callsSingList es s).1 = true := by
  cases es with
  | nil => simp [pureList, callsSingList]
  | cons e es =>
    simp only [pureList, Bool.and_eq_true] at h
    simp only [callsSingList]
    cases he : callsSing e s with
    | mk e1 s1 =>
      cases hes : callsSingList es s1 with
      | mk es1 s2 =>
        have h1 := pureSing e s h.1
        rw [he] at h1
        have h2 := pureSingList es s1 h.2
        rw [hes] at h2
        simpa [pureList] using And.intro h1 h2
termination_by sizeOf es
decreasing_by all_goals (subst_vars; simp_wf; try omega)
end
/-- The direct-call pass preserves purity of every input expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_pure"]
theorem calls_pure (xs : List Exp) (g : State) (es : List Exp) (g1 : State)
    (h : xs.all ClosLang.pure = true ∧ calls xs g = (es, g1)) :
    es.all ClosLang.pure = true := by
  have p := pureSingList xs g (by simpa [pureList_eq_all] using h.1)
  have run : callsSingList xs g = (es, g1) := h.2
  rw [run] at p
  simpa [pureList_eq_all] using p

/-- The singleton form of direct-call purity preservation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_pure_sing"]
theorem calls_pure_sing (x1 : Exp) (g : State) (e1 : Exp) (g1 : State)
    (h : ClosLang.pure x1 = true ∧ calls [x1] g = ([e1], g1)) :
    ClosLang.pure e1 = true := by
  have p := calls_pure [x1] g [e1] g1 (by simpa using h)
  simpa using p
end Flapjack.Compiler.Backend.ClosCall
