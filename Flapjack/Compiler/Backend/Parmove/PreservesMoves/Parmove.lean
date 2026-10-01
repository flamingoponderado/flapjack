import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Pmov
import Flapjack.Compiler.Backend.Parmove.PmovFinal

namespace Flapjack.Compiler.Backend.Parmove

/-- Each non-self input move's real destination occurs in the actual compiled
move sequence. Initial scheduler well-formedness and terminal shape are derived
internally. The canonical scheduler's computational `DecidableEq` instance adds
no equality-law, target-result, or scratch-safety premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_preserves_moves"]
theorem parmovePreservesMoves {α : Type} [DecidableEq α]
    (moves : List (α × α)) (x y : α) :
    windmill moves ∧ (x, y) ∈ moves ∧ x ≠ y →
      some x ∈ (parmove moves).map Prod.fst := by
  rintro ⟨valid, member, different⟩
  let lifted := moves.map (fun move => (some move.1, some move.2))
  let initial : State α := (lifted, [], [])
  have liftedValid : windmill lifted := by
    have h : ((moves.map Prod.fst).map some).Nodup :=
      valid.map some (fun _ _ different equal => different (Option.some.inj equal))
    simpa [windmill, lifted, List.map_map, Function.comp_def] using h
  have initialValid : wf initial := by
    apply wf_init lifted
    refine ⟨liftedValid, ?_, ?_⟩
    · intro move hm
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp hm
      rfl
    · intro move hm
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp hm
      rfl
  have liftedMember : (some x, some y) ∈ lifted := by
    change (some x, some y) ∈ moves.map (fun move => (some move.1, some move.2))
    exact List.mem_map.mpr ⟨(x, y), member, rfl⟩
  have initialMember : (some x, some y) ∈ stateToList initial := by
    simpa [initial, stateToList] using liftedMember
  have retained := pmovPreservesMoves (some x) (some y) initial
    ⟨initialValid, initialMember, fun h => different (Option.some.inj h)⟩
  obtain ⟨emitted, final⟩ := pmov_final initial
  have outputMember : some x ∈ emitted.map Prod.fst := by
    simpa [final, stateToList] using retained
  change some x ∈ ((pmov initial).2.2.reverse).map Prod.fst
  rw [final]
  simpa [List.map_reverse] using outputMember

end Flapjack.Compiler.Backend.Parmove
