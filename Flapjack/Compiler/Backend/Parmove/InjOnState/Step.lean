import Flapjack.Compiler.Backend.Parmove.InjOnState
import Flapjack.Compiler.Backend.Parmove.Steps

namespace Flapjack.Compiler.Backend.Parmove

/-- HOL `step_inj_on_state` (`parmoveScript.sml:1098`): every primitive move
step preserves injectivity on the endpoint state. No scratch/reserved distinctness
or global-injectivity premise is added: each step only permutes or drops state
entries, and the fresh `none` introduced by the save step is discharged from the
`none`-iff conjunct of `injOnState`. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_inj_on_state"]
theorem stepInjOnState {α β : Type} (f : Option α → Option β) (first second : State α) :
    Step first second → injOnState f first → injOnState f second := by
  intro transition h
  simp only [injOnState] at h ⊢
  refine ⟨?_, h.2⟩
  intro x y hxy
  have hsub : ∀ z, z ∈ (stateToList second).map Prod.fst ++ (stateToList second).map Prod.snd →
      z ∈ (stateToList first).map Prod.fst ++ (stateToList first).map Prod.snd ∨ z = none := by
    cases transition <;>
      simp only [stateToList, List.map_append, List.mem_append, List.mem_map,
        List.mem_cons, List.not_mem_nil] <;>
      grind
  rcases hsub x hxy.1 with hx | hx
  · rcases hsub y hxy.2.1 with hy | hy
    · exact h.1 x y ⟨hx, hy, hxy.2.2⟩
    · rw [hy] at hxy ⊢
      have hfn : f none = none := (h.2 none).mpr rfl
      rw [hfn] at hxy
      exact (h.2 x).mp hxy.2.2
  · rw [hx] at hxy ⊢
    have hfn : f none = none := (h.2 none).mpr rfl
    rw [hfn] at hxy
    exact ((h.2 y).mp hxy.2.2.symm).symm

end Flapjack.Compiler.Backend.Parmove
