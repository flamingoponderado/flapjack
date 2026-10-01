import Flapjack.Compiler.Backend.Parmove.Steps
import Flapjack.Compiler.Backend.Parmove.MapState
import Flapjack.Compiler.Backend.Parmove.InjOnState

namespace Flapjack.Compiler.Backend.Parmove

/-- Scoped endpoint injectivity transports all six literal primitive scheduler
rules. Only the source-state injectivity and global scratch preservation/reflection
from HOL are required, with independent input/output register carriers. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_MAP_INJ"]
theorem stepMapInj {α β : Type} (f : Option α → Option β)
    (first second : State α) :
    Step first second → injOnState f first →
      Step (mapState f first) (mapState f second) := by
  intro transition injective
  have scratch : f none = none := injective.2 none |>.mpr rfl
  cases transition with
  | removeSelf r before after active emitted =>
      simpa [mapState, List.map_append] using
        Step.removeSelf (f r) (before.map (Prod.map f f)) (after.map (Prod.map f f))
          (active.map (Prod.map f f)) (emitted.map (Prod.map f f))
  | start d s before after emitted =>
      simpa [mapState, List.map_append] using
        Step.start (f d) (f s) (before.map (Prod.map f f)) (after.map (Prod.map f f))
          (emitted.map (Prod.map f f))
  | extend d r s before after active emitted =>
      simpa [mapState, List.map_append] using
        Step.extend (f d) (f r) (f s) (before.map (Prod.map f f))
          (after.map (Prod.map f f)) (active.map (Prod.map f f))
          (emitted.map (Prod.map f f))
  | save d s pending active emitted =>
      simpa [mapState, List.map_append, scratch] using
        Step.save (f d) (f s) (pending.map (Prod.map f f))
          (active.map (Prod.map f f)) (emitted.map (Prod.map f f))
  | emitHead d0 dn s0 sn pending active emitted noRead distinct =>
      have noReadMapped : f dn ∉ (pending.map (Prod.map f f)).map Prod.snd := by
        intro member
        rw [List.map_map] at member
        obtain ⟨move, present, equal⟩ := List.mem_map.mp member
        have source : move.2 ∈ pending.map Prod.snd := List.mem_map.mpr ⟨move, present, rfl⟩
        have same : dn = move.2 := injective.1 dn move.2
          ⟨by simp [stateToList], by simp [stateToList, source], equal.symm⟩
        exact noRead (same ▸ source)
      have distinctMapped : f dn ≠ f s0 := by
        intro equal
        exact distinct (injective.1 dn s0
          ⟨by simp [stateToList], by simp [stateToList], equal⟩)
      simpa [mapState, List.map_append] using
        Step.emitHead (f d0) (f dn) (f s0) (f sn) (pending.map (Prod.map f f))
          (active.map (Prod.map f f)) (emitted.map (Prod.map f f)) noReadMapped distinctMapped
  | emitLast d s pending emitted noRead =>
      have noReadMapped : f d ∉ (pending.map (Prod.map f f)).map Prod.snd := by
        intro member
        rw [List.map_map] at member
        obtain ⟨move, present, equal⟩ := List.mem_map.mp member
        have source : move.2 ∈ pending.map Prod.snd := List.mem_map.mpr ⟨move, present, rfl⟩
        have same : d = move.2 := injective.1 d move.2
          ⟨by simp [stateToList], by simp [stateToList, source], equal.symm⟩
        exact noRead (same ▸ source)
      simpa [mapState, List.map_append] using
        Step.emitLast (f d) (f s) (pending.map (Prod.map f f))
          (emitted.map (Prod.map f f)) noReadMapped

end Flapjack.Compiler.Backend.Parmove
