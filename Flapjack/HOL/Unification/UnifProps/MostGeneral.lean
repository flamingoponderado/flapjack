module

public import Flapjack.HOL.Unification.UnifProps.Extend
public import Flapjack.HOL.Unification.UnifProps.Soundness

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Most-generality of the guarded recursive unifier model. This supports the
    HOL unifier proof; the option-wrapped map result is not yet qualified. -/
theorem tunifyAuxMostGeneral {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (a b : Term α) (sx : HolFiniteMapExact Nat (Term α))
    (s2 : HolFiniteMapExact Nat (Term α))
    (h : wfs s ∧ tunifyAux s a b = some sx ∧ wfs s2 ∧
      walkstar s2 (walkstar s a) = walkstar s2 (walkstar s b)) :
    ∀ t, walkstar s2 (walkstar sx t) = walkstar s2 (walkstar s t) := by
  classical
  have extension (s s2 : HolFiniteMapExact Nat (Term α)) (v : Nat) (term : Term α)
      (hw : wfs s) (hw2 : wfs s2) (hout : wfs (s.updateEq (v, term)))
      (fresh : v ∉ s.domain)
      (eq : walkstar s2 (walkstar s (.var v)) = walkstar s2 (walkstar s term)) :
      ∀ t, walkstar s2 (walkstar (s.updateEq (v, term)) t) = walkstar s2 (walkstar s t) := by
    have var : walkstar s (.var v) = .var v := by
      rw [walkstarEq s hw (.var v)]
      simp only [walk, notFdomVwalk s v ⟨hw, fresh⟩]
    apply walkstarExtend s2 s v term
    exact ⟨hw2, hout, fresh, by simpa [var] using eq⟩
  have all : ∀ s (a b : Term α) sx s2, wfs s → tunifyAux s a b = some sx → wfs s2 →
      walkstar s2 (walkstar s a) = walkstar s2 (walkstar s b) →
      ∀ t, walkstar s2 (walkstar sx t) = walkstar s2 (walkstar s t) := by
    apply tunifyAuxInd
    intro s a b ih sx s2 hw result hw2 eq
    have up := tunifyAuxUP s a b sx ⟨hw, result⟩
    have eqWalk : walkstar s2 (walkstar s (walk s a)) = walkstar s2 (walkstar s (walk s b)) := by
      simpa only [walkstarWalk s a hw, walkstarWalk s b hw] using eq
    rw [tunifyAuxEquation s a b hw] at result
    cases la : walk s a <;> cases lb : walk s b <;> simp only [la, lb] at result eqWalk
    case var.var =>
      rename_i v u
      split at result
      · simp only [Option.some.injEq] at result
        subst sx
        intro t
        rfl
      · simp only [Option.some.injEq] at result
        subst sx
        exact extension s s2 v (.var u) hw hw2 up.1 (walkToVar s a v ⟨hw, la⟩).1 eqWalk
    case var.pair | var.const =>
      split at result
      · contradiction
      · simp only [Option.some.injEq] at result
        subst sx
        exact extension s s2 _ _ hw hw2 up.1 (walkToVar s a _ ⟨hw, la⟩).1 eqWalk
    case pair.var | const.var =>
      split at result
      · contradiction
      · simp only [Option.some.injEq] at result
        subst sx
        exact extension s s2 _ _ hw hw2 up.1 (walkToVar s b _ ⟨hw, lb⟩).1 eqWalk.symm
    case pair.pair =>
      rename_i a1 a2 b1 b2
      cases head : tunifyAux s a1 b1 with
      | none => simp [head] at result
      | some mid =>
        simp only [head, Option.bind] at result
        have midWfs := (tunifyAuxUP s a1 b1 mid ⟨hw, head⟩).1
        rw [walkstarEq s hw (.pair a1 a2), walkstarEq s hw (.pair b1 b2)] at eqWalk
        simp only [walk] at eqWalk
        rw [walkstarEq s2 hw2 (.pair _ _), walkstarEq s2 hw2 (.pair _ _)] at eqWalk
        simp only [walk, Term.pair.injEq] at eqWalk
        have first := ih.2 a1 a2 b1 b2 ⟨hw, la, lb⟩ mid s2 hw head hw2 eqWalk.1
        have secondEq : walkstar s2 (walkstar mid a2) = walkstar s2 (walkstar mid b2) := by
          rw [first a2, first b2]
          exact eqWalk.2
        have second := ih.1 a1 a2 b1 b2 mid ⟨hw, la, lb, head⟩ sx s2 midWfs result hw2 secondEq
        intro t
        rw [second t, first t]
    case pair.const | const.pair => contradiction
    case const.const =>
      split at result
      · simp only [Option.some.injEq] at result
        subst sx
        intro t
        rfl
      · contradiction
  exact all s a b sx s2 h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Most-generality for the selected guarded unifier. This is untagged until
    the option-wrapped canonical finite-map result has a reviewed qualifier. -/
theorem specifiedUnifyMostGeneral {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (a b : Term α) (sx : HolFiniteMapExact Nat (Term α))
    (s2 : HolFiniteMapExact Nat (Term α))
    (h : wfs s ∧ specifiedUnify s a b = some sx ∧ wfs s2 ∧
      walkstar s2 (walkstar s a) = walkstar s2 (walkstar s b)) :
    ∀ t, walkstar s2 (walkstar sx t) = walkstar s2 (walkstar s t) := by
  apply tunifyAuxMostGeneral s a b sx s2
  refine ⟨h.1, ?_, h.2.2⟩
  rw [← specifiedUnifyEqAux s a b h.1]
  exact h.2.1

end Flapjack.HOL.Unification
