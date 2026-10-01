import Flapjack.Compiler.Backend.Parmove.FstepMapInj
import Flapjack.Compiler.Backend.Parmove.DStepsSteps
import Flapjack.Compiler.Backend.Parmove.FstepDstep
import Flapjack.Compiler.Backend.Parmove.InjOnState.Steps

namespace Flapjack.Compiler.Backend.Parmove

/-- The original deterministic scheduler commutes with a renaming that is
injective on the well-formed initial state. The well-formedness is carried
along the deterministic closure via `wf_steps`, and the injectivity via
`steps_inj_on_state`, rather than assumed at the recursive state. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_MAP_INJ"]
theorem pmovMapInj {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : Option α → Option β) (state : State α) :
    wf state → injOnState f state →
      pmov (mapState f state) = mapState f (pmov state) := by
  intro valid inj
  refine pmov.induct (motive := fun x => wf x → injOnState f x →
    pmov (mapState f x) = mapState f (pmov x)) ?_ ?_ state valid inj
  · intro x hfin _hvalid _hinj
    obtain ⟨pending, active, emitted⟩ := x
    simp only at hfin
    obtain ⟨rfl, rfl⟩ := hfin
    have hpmov : pmov ([], [], emitted) = ([], [], emitted) := by
      rw [pmov, dif_pos (show ([], [], emitted).1 = [] ∧ ([], [], emitted).2.1 = [] from ⟨rfl, rfl⟩)]
    have hmap : pmov (mapState f ([], [], emitted)) = mapState f ([], [], emitted) := by
      rw [pmov]
      rw [dif_pos]
      exact ⟨rfl, rfl⟩
    rw [hpmov, hmap]
  · intro x hunfin ih hvalid hinj
    obtain ⟨pending, active, emitted⟩ := x
    have hne : ∀ e : List (Move α), (pending, active, emitted) ≠ ([], [], e) := by
      intro e he
      apply hunfin
      rw [he]
      exact ⟨rfl, rfl⟩
    have hdstep := fstepDstep (α := α) (pending, active, emitted) hne
    have hDSteps : DSteps (pending, active, emitted) (fstep (pending, active, emitted)) :=
      Relation.ReflTransGen.single hdstep
    have hSteps := dsteps_steps (pending, active, emitted) (fstep (pending, active, emitted)) hDSteps hvalid
    have hvalid' := wf_steps (pending, active, emitted) (fstep (pending, active, emitted)) ⟨hvalid, hSteps⟩
    have hinj' := stepsInjOnState f (pending, active, emitted) (fstep (pending, active, emitted)) ⟨hinj, hSteps⟩
    have ihx := ih hvalid' hinj'
    have hpX : pmov (pending, active, emitted) = pmov (fstep (pending, active, emitted)) := by
      rw [pmov, dif_neg hunfin]
    have hpm : pmov (mapState f (pending, active, emitted)) =
        pmov (fstep (mapState f (pending, active, emitted))) := by
      rw [pmov]
      rw [dif_neg]
      intro hcon
      apply hunfin
      obtain ⟨hp, ha⟩ := hcon
      simp only [mapState, Prod.map_fst, Prod.map_snd, List.map_eq_nil_iff] at hp ha
      exact ⟨hp, ha⟩
    have hfstep := fstepMapInj f (pending, active, emitted) hinj
    rw [hpX, hpm, hfstep, ihx]

end Flapjack.Compiler.Backend.Parmove
