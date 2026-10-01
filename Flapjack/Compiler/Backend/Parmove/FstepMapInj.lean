import Flapjack.Compiler.Backend.Parmove.InjOnState
import Flapjack.Compiler.Backend.Parmove.MapState

namespace Flapjack.Compiler.Backend.Parmove

private theorem splitSource_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : Option α → Option β) (destination : Option α) (moves : List (Move α))
    (reflect : ∀ move ∈ moves, f move.2 = f destination ↔ move.2 = destination) :
    splitSource (f destination) (moves.map (Prod.map f f)) =
      Prod.map (List.map (Prod.map f f)) (List.map (Prod.map f f))
        (splitSource destination moves) := by
  induction moves with
  | nil => rfl
  | cons move moves ih =>
      have head := reflect move (by simp)
      have tail := ih (fun m hm => reflect m (by simp [hm]))
      simp only [List.map_cons, splitSource, Prod.map_snd]
      by_cases same : move.2 = destination
      · simp [same]
      · simp [same, mt head.mp same, tail]

private theorem frontLast_map {α β : Type} (f : Option α → Option β)
    (head : Move α) (tail : List (Move α)) :
    frontLast (Prod.map f f head) (tail.map (Prod.map f f)) =
      Prod.map (List.map (Prod.map f f)) (Prod.map f f) (frontLast head tail) := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest ih => simp [frontLast, ih]

private theorem endpoint_eq {α β : Type} (f : Option α → Option β)
    (state : State α) (valid : injOnState f state)
    (a b : Move α) (ha : a ∈ stateToList state) (hb : b ∈ stateToList state) :
    f a.2 = f b.1 ↔ a.2 = b.1 := by
  constructor
  · intro equal
    exact valid.1 a.2 b.1 ⟨List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨a, ha, rfl⟩)), List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨b, hb, rfl⟩)), equal⟩
  · exact congrArg f

/-- The original deterministic step commutes with a renaming injective only
on the current state's endpoints, preserving and reflecting the temporary.
The input and output payload carriers are independent. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "fstep_MAP_INJ"]
theorem fstepMapInj {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : Option α → Option β) (state : State α) (valid : injOnState f state) :
    fstep (mapState f state) = mapState f (fstep state) := by
  rcases state with ⟨pending, active, emitted⟩
  have temporary : f none = none := (valid.2 none).mpr rfl
  cases active with
  | nil =>
      cases pending with
      | nil => rfl
      | cons move pending =>
          rcases move with ⟨destination, source⟩
          have reflect := endpoint_eq f ( (destination, source) :: pending, [], emitted)
            valid (destination, source) (destination, source)
            (by simp [stateToList]) (by simp [stateToList])
          simp only [mapState, Prod.map, List.map_cons, List.map_nil, fstep]
          by_cases same : source = destination
          · simp [same]
          · simp [same, mt reflect.mp same]
  | cons move active =>
      rcases move with ⟨destination, source⟩
      have search := splitSource_map f destination pending (fun m hm =>
        endpoint_eq f (pending, (destination, source) :: active, emitted) valid m
          (destination, source) (by simp [stateToList, hm]) (by simp [stateToList]))
      simp only [mapState, Prod.map, List.map_cons, fstep]
      rw [search]
      cases splitEq : splitSource destination pending with
      | mk before after =>
          cases after with
          | cons next rest => simp [List.map_append]
          | nil =>
              cases active with
              | nil => simp
              | cons head tail =>
                  have lastMember : (frontLast head tail).2 ∈ head :: tail := by
                    rw [← frontLast_append head tail]
                    simp
                  have reflect := endpoint_eq f
                    (pending, (destination, source) :: head :: tail, emitted) valid
                    (frontLast head tail).2 (destination, source)
                    (List.mem_append.mpr (Or.inl (List.mem_append.mpr
                      (Or.inr (List.mem_cons_of_mem _ lastMember)))))
                    (by simp [stateToList])
                  by_cases same : (frontLast head tail).2.2 = destination
                  · simp [frontLast_map, same, temporary, List.map_append]
                  · simp [frontLast_map, same, mt reflect.mp same]

end Flapjack.Compiler.Backend.Parmove
