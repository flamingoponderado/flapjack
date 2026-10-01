import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Compiler.Backend.Parmove

/-- Flapjack infrastructure collecting destinations in the three native state
lists. It has no standalone HOL declaration. -/
private def destinations {α : Type} (state : State α) : List (Option α) :=
  state.1.map Prod.fst ++ state.2.1.map Prod.fst ++ state.2.2.map Prod.fst

/-- One-step real-destination preservation. This is proof infrastructure for
HOL's pmov membership theorem, not a separate HOL declaration. -/
private theorem fstep_destination_mem {α : Type} [DecidableEq α]
    (state : State α) (v : Option α) (hv : v ≠ none) :
    v ∈ destinations (fstep state) → v ∈ destinations state := by
  obtain ⟨pending, active, emitted⟩ := state
  cases active with
  | nil =>
    cases pending with
    | nil => simp [fstep, destinations]
    | cons move pending =>
      obtain ⟨d, s⟩ := move
      simp only [fstep]
      split <;> simp_all [destinations] <;> grind
  | cons move active =>
    obtain ⟨d, s⟩ := move
    have partition := congrArg (fun xs => v ∈ xs.map Prod.fst) (splitSource_append d pending)
    simp only [List.map_append, List.mem_append] at partition
    simp only [fstep]
    cases hsuffix : (splitSource d pending).2 with
    | cons next rest =>
      simp only [hsuffix, List.map_cons, List.mem_cons] at partition
      simp only [destinations, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      grind
    | nil =>
      cases active with
      | nil => simp [destinations]
      | cons head tail =>
        have front := congrArg (fun xs => v ∈ xs.map Prod.fst) (frontLast_append head tail)
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at front
        simp only
        split <;> simp only [destinations, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] <;> grind

/-- HOL arbitrary-state pmov real-destination membership. No well-formedness,
termination, result-shape, or algorithm simulation premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_FST_SND_SND_pmov"]
theorem memMapFstSndSndPmov {α : Type} [DecidableEq α] :
    ∀ (state : State α) (x : α),
      some x ∈ (pmov state).2.2.map Prod.fst →
      some x ∈ (state.1 ++ state.2.1 ++ state.2.2).map Prod.fst := by
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
    change some x ∈ destinations state
    apply fstep_destination_mem state (some x) (by simp)
    simpa only [destinations, List.map_append] using hi

end Flapjack.Compiler.Backend.Parmove
