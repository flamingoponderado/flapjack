module

public import Flapjack.HOL.Unification.UnifProps.MostGeneral
public import Flapjack.HOL.Unification.UnifProps.Occurs

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Completeness of the guarded recursive model. This supports HOL eqs_unify;
    the option-wrapped finite-map result still needs a reviewed qualifier. -/
theorem tunifyAuxComplete {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 : Term α) (s2 : HolFiniteMapExact Nat (Term α))
    (h : wfs s ∧ wfs s2 ∧ walkstar s2 (walkstar s t1) = walkstar s2 (walkstar s t2)) :
    ∃ sx, tunifyAux s t1 t2 = some sx := by
  classical
  have all : ∀ s (a b : Term α) s2, wfs s → wfs s2 →
      walkstar s2 (walkstar s a) = walkstar s2 (walkstar s b) →
      ∃ sx, tunifyAux s a b = some sx := by
    apply tunifyAuxInd
    intro s a b ih s2 hw hw2 eq
    have eqWalk : walkstar s2 (walkstar s (walk s a)) = walkstar s2 (walkstar s (walk s b)) := by
      simpa only [walkstarWalk s a hw, walkstarWalk s b hw] using eq
    rw [tunifyAuxEquation s a b hw]
    cases la : walk s a <;> cases lb : walk s b <;> simp only [la, lb] at eqWalk ⊢
    case var.var =>
      exact ⟨_, rfl⟩
    case var.pair =>
      rename_i v l r
      have fresh := (walkToVar s a v ⟨hw, la⟩).1
      have var : walkstar s (.var v) = .var v := by
        rw [walkstarEq s hw (.var v)]
        simp only [walk, notFdomVwalk s v ⟨hw, fresh⟩]
      have no : ¬ Oc s (.pair l r) v := by
        intro oc
        exact ocSubtermNeq s _ _ s2 ⟨oc, by intro w; simp, hw, hw2⟩ (by simpa only [var] using eqWalk)
      simp [no]
    case var.const =>
      rename_i v c
      have fresh := (walkToVar s a v ⟨hw, la⟩).1
      have var : walkstar s (.var v) = .var v := by
        rw [walkstarEq s hw (.var v)]
        simp only [walk, notFdomVwalk s v ⟨hw, fresh⟩]
      have no : ¬ Oc s (.const c) v := by
        intro oc
        exact ocSubtermNeq s _ _ s2 ⟨oc, by intro w; simp, hw, hw2⟩ (by simpa only [var] using eqWalk)
      simp [no]
    case pair.var =>
      rename_i l r v
      have fresh := (walkToVar s b v ⟨hw, lb⟩).1
      have var : walkstar s (.var v) = .var v := by
        rw [walkstarEq s hw (.var v)]
        simp only [walk, notFdomVwalk s v ⟨hw, fresh⟩]
      have no : ¬ Oc s (.pair l r) v := by
        intro oc
        exact ocSubtermNeq s _ _ s2 ⟨oc, by intro w; simp, hw, hw2⟩ (by simpa only [var] using eqWalk.symm)
      simp [no]
    case const.var =>
      rename_i c v
      have fresh := (walkToVar s b v ⟨hw, lb⟩).1
      have var : walkstar s (.var v) = .var v := by
        rw [walkstarEq s hw (.var v)]
        simp only [walk, notFdomVwalk s v ⟨hw, fresh⟩]
      have no : ¬ Oc s (.const c) v := by
        intro oc
        exact ocSubtermNeq s _ _ s2 ⟨oc, by intro w; simp, hw, hw2⟩ (by simpa only [var] using eqWalk.symm)
      simp [no]
    case pair.pair =>
      rename_i a1 a2 b1 b2
      rw [walkstarEq s hw (.pair a1 a2), walkstarEq s hw (.pair b1 b2)] at eqWalk
      simp only [walk] at eqWalk
      rw [walkstarEq s2 hw2 (.pair _ _), walkstarEq s2 hw2 (.pair _ _)] at eqWalk
      simp only [walk, Term.pair.injEq] at eqWalk
      obtain ⟨mid, head⟩ := ih.2 a1 a2 b1 b2 ⟨hw, la, lb⟩ s2 hw hw2 eqWalk.1
      have midWfs := (tunifyAuxUP s a1 b1 mid ⟨hw, head⟩).1
      have mgu := tunifyAuxMostGeneral s a1 b1 mid s2 ⟨hw, head, hw2, eqWalk.1⟩
      have tailEq : walkstar s2 (walkstar mid a2) = walkstar s2 (walkstar mid b2) := by
        rw [mgu a2, mgu b2]
        exact eqWalk.2
      obtain ⟨sx, tail⟩ := ih.1 a1 a2 b1 b2 mid ⟨hw, la, lb, head⟩ s2 midWfs hw2 tailEq
      exact ⟨sx, by simpa [head] using tail⟩
    case pair.const =>
      rename_i l r c
      rw [walkstarEq s hw (.pair l r), walkstarEq s hw (.const c)] at eqWalk
      simp only [walk] at eqWalk
      rw [walkstarEq s2 hw2 (.pair _ _), walkstarEq s2 hw2 (.const c)] at eqWalk
      simp [walk] at eqWalk
    case const.pair =>
      rename_i c l r
      rw [walkstarEq s hw (.const c), walkstarEq s hw (.pair l r)] at eqWalk
      simp only [walk] at eqWalk
      rw [walkstarEq s2 hw2 (.const c), walkstarEq s2 hw2 (.pair _ _)] at eqWalk
      simp [walk] at eqWalk
    case const.const =>
      rename_i c d
      rw [walkstarEq s hw (.const c), walkstarEq s hw (.const d)] at eqWalk
      simp only [walk] at eqWalk
      rw [walkstarEq s2 hw2 (.const c), walkstarEq s2 hw2 (.const d)] at eqWalk
      simp only [walk, Term.const.injEq] at eqWalk
      simp [eqWalk]
  exact all s t1 t2 s2 h.1 h.2.1 h.2.2

/-- Completeness of the selected guarded model. It remains untagged until
    the option-wrapped finite-map result has a reviewed representation. -/
theorem specifiedUnifyComplete {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 : Term α) (s2 : HolFiniteMapExact Nat (Term α))
    (h : wfs s ∧ wfs s2 ∧ walkstar s2 (walkstar s t1) = walkstar s2 (walkstar s t2)) :
    ∃ sx, specifiedUnify s t1 t2 = some sx := by
  obtain ⟨sx, hsx⟩ := tunifyAuxComplete s t1 t2 s2 h
  exact ⟨sx, by rw [specifiedUnifyEqAux s t1 t2 h.1]; exact hsx⟩

end Flapjack.HOL.Unification
