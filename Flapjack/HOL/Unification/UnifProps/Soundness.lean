module

public import Flapjack.HOL.Unification.UnifProps
public import Flapjack.HOL.Unification.UnifDef.Choice

@[expose] public section

/-! Soundness of the well-founded unifier model. -/
namespace Flapjack.HOL.Unification

private theorem normalizeUpdate {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat)
    (t : Term α) (hw : wfs (s.updateEq (v, t))) :
    walkstar (s.updateEq (v, t)) (.var v) = walkstar (s.updateEq (v, t)) t := by
  rw [← walkstarWalk (s.updateEq (v, t)) (.var v) hw]
  simp only [walk]
  rw [vwalkEq _ hw v]
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ↓reduceIte]
  cases t with
  | var u =>
    simpa [walk] using walkstarWalk (s.updateEq (v, .var u)) (.var u) hw
  | pair l r => rfl
  | const c => rfl

/-- Soundness of the restricted recursion model. This is a prerequisite for
    the source unifier theorem, not HOL unify_unifier itself: HOL names its
    specified unifier and its option-wrapped map result needs qualification. -/
theorem tunifyAuxSound {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α)
    (sx : HolFiniteMapExact Nat (Term α)) (h : wfs s ∧ tunifyAux s t1 t2 = some sx) :
    wfs sx ∧ s.submap sx ∧ walkstar sx t1 = walkstar sx t2 := by
  classical
  have all : ∀ s (a b : Term α) sx, wfs s → tunifyAux s a b = some sx →
      wfs sx ∧ s.submap sx ∧ walkstar sx a = walkstar sx b := by
    apply tunifyAuxInd
    intro s a b ih sx hw result
    have up := tunifyAuxUP s a b sx ⟨hw, result⟩
    refine ⟨up.1, up.2.1, ?_⟩
    rw [walkstarWalkSubmap s sx a ⟨up.2.1, up.1⟩,
      walkstarWalkSubmap s sx b ⟨up.2.1, up.1⟩]
    rw [tunifyAuxEquation s a b hw] at result
    cases la : walk s a <;> cases lb : walk s b <;>
      simp only [la, lb] at result ⊢
    case var.var =>
      rename_i v u
      split at result
      · rename_i eq
        subst u
        rfl
      · simp only [Option.some.injEq] at result
        subst sx
        exact normalizeUpdate s v (.var u) up.1
    case var.pair | var.const =>
      split at result
      · contradiction
      · simp only [Option.some.injEq] at result
        subst sx
        exact normalizeUpdate s _ _ up.1
    case pair.var | const.var =>
      split at result
      · contradiction
      · simp only [Option.some.injEq] at result
        subst sx
        exact (normalizeUpdate s _ _ up.1).symm
    case pair.pair =>
      rename_i a1 a2 b1 b2
      cases head : tunifyAux s a1 b1 with
      | none => simp [head] at result
      | some mid =>
        have first := ih.2 a1 a2 b1 b2 ⟨hw, la, lb⟩ mid hw head
        simp only [head, Option.bind] at result
        have second := ih.1 a1 a2 b1 b2 mid ⟨hw, la, lb, head⟩ sx first.1 result
        have lifted : walkstar sx a1 = walkstar sx b1 := by
          calc
            walkstar sx a1 = walkstar sx (walkstar mid a1) := walkstarSubmap mid sx a1 ⟨second.2.1, second.1⟩
            _ = walkstar sx (walkstar mid b1) := by rw [first.2.2]
            _ = walkstar sx b1 := (walkstarSubmap mid sx b1 ⟨second.2.1, second.1⟩).symm
        rw [walkstarEq sx up.1 (.pair a1 a2), walkstarEq sx up.1 (.pair b1 b2)]
        simp only [walk, lifted, second.2.2]
    case pair.const | const.pair => contradiction
    case const.const =>
      split at result
      · rename_i eq
        subst_vars
        rfl
      · contradiction
  exact all s t1 t2 sx h.1 h.2


end Flapjack.HOL.Unification
