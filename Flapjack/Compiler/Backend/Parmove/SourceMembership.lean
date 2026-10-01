import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Compiler.Backend.Parmove

/-- Flapjack infrastructure collecting sources in the three native state
lists. It has no standalone HOL declaration. -/
private def sources {α : Type} (state : State α) : List (Option α) :=
  state.1.map Prod.snd ++ state.2.1.map Prod.snd ++ state.2.2.map Prod.snd

/-- One-step real-source preservation. This is proof infrastructure for
HOL's pmov membership theorem, not a separate HOL declaration. -/
private theorem fstep_source_mem {α : Type} [DecidableEq α]
    (state : State α) (v : Option α) (hv : v ≠ none) :
    v ∈ sources (fstep state) → v ∈ sources state := by
  obtain ⟨pending, active, emitted⟩ := state
  cases active with
  | nil =>
    cases pending with
    | nil => simp [fstep, sources]
    | cons move pending =>
      obtain ⟨d, s⟩ := move
      simp only [fstep]
      split <;> simp_all [sources] <;> grind
  | cons move active =>
    obtain ⟨d, s⟩ := move
    have partition := congrArg (fun xs => v ∈ xs.map Prod.snd) (splitSource_append d pending)
    simp only [List.map_append, List.mem_append] at partition
    simp only [fstep]
    cases hsuffix : (splitSource d pending).2 with
    | cons next rest =>
      simp only [hsuffix, List.map_cons, List.mem_cons] at partition
      simp only [sources, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      grind
    | nil =>
      cases active with
      | nil => simp [sources]
      | cons head tail =>
        have front := congrArg (fun xs => v ∈ xs.map Prod.snd) (frontLast_append head tail)
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at front
        simp only
        split <;> simp only [sources, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] <;> grind

/-- HOL arbitrary-state pmov real-source membership. No well-formedness,
termination, result-shape, or algorithm simulation premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_SND_SND_SND_pmov"]
theorem memMapSndSndSndPmov {α : Type} [DecidableEq α] :
    ∀ (state : State α) (x : α),
      some x ∈ (pmov state).2.2.map Prod.snd →
      some x ∈ (state.1 ++ state.2.1 ++ state.2.2).map Prod.snd := by
  intro state
  induction state using pmov.induct with
  | case1 state finished =>
    rw [pmov.eq_def, dif_pos finished]
    intro x hx
    simp only [List.map_append, List.mem_append]
    exact Or.inr hx
  | case2 state unfinished ih =>
    rw [pmov.eq_def, dif_neg unfinished]
    intro x hx
    have hi := ih x hx
    simp only [List.map_append]
    change some x ∈ sources state
    apply fstep_source_mem state (some x) (by simp)
    simpa only [sources, List.map_append] using hi

end Flapjack.Compiler.Backend.Parmove
