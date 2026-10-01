import Flapjack.Compiler.Backend.Parmove.UpdateLemmas

namespace Flapjack.Compiler.Backend.Parmove

/-- Injective renaming on the listed destination/source domain preserves
parallel semantics at a listed destination. The renaming's source and target
register carriers and the environment value carrier are independent. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_MAP_INJ"]
theorem parsemMapInj {α γ β : Type} [DecidableEq α] [DecidableEq γ]
    (moves : List (α × α)) (f : α → γ) (env : γ → β)
    (valid : windmill moves)
    (injective : ∀ a ∈ moves.map Prod.fst ++ moves.map Prod.snd,
      ∀ b ∈ moves.map Prod.fst ++ moves.map Prod.snd, f a = f b → a = b)
    (x : α) (member : x ∈ moves.map Prod.fst) :
    parsem (moves.map (fun move => (f move.1, f move.2))) env (f x) =
      parsem moves (env ∘ f) x := by
  induction moves with
  | nil => simp at member
  | cons move moves ih =>
      rcases move with ⟨destination, source⟩
      have parts : destination ∉ moves.map Prod.fst ∧ windmill moves := by
        simpa [windmill] using valid
      have fresh : f destination ∉ (moves.map (fun move => (f move.1, f move.2))).map Prod.fst := by
        intro found
        obtain ⟨pair, hp, heq⟩ := List.mem_map.mp found
        obtain ⟨orig, ho, hor⟩ := List.mem_map.mp hp
        subst pair
        have hd : destination = orig.1 := injective destination (by simp)
          orig.1 (by simp only [List.map_cons, List.mem_append, List.mem_cons]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨orig,ho,rfl⟩))) heq.symm
        exact parts.1 (hd ▸ List.mem_map.mpr ⟨orig,ho,rfl⟩)
      rw [List.map_cons, parsem_cons _ _ _ _ fresh,
        parsem_cons _ _ _ _ parts.1]
      have tailInj : ∀ a ∈ moves.map Prod.fst ++ moves.map Prod.snd,
          ∀ b ∈ moves.map Prod.fst ++ moves.map Prod.snd, f a = f b → a = b := by
        intro a ha b hb
        apply injective a _ b _
        · simpa only [List.map_cons, List.mem_append, List.mem_cons] using
            (List.mem_append.mp ha).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
        · simpa only [List.map_cons, List.mem_append, List.mem_cons] using
            (List.mem_append.mp hb).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
      have casesX : x = destination ∨ x ∈ moves.map Prod.fst := by simpa using member
      rcases casesX with rfl | hx
      · simp [updateEnv]
      · have neq : f x ≠ f destination := by
          intro equal
          have same := injective x (by simp [hx]) destination (by simp) equal
          exact parts.1 (same ▸ hx)
        simp only [updateEnv, if_neg neq]
        have xd : x ≠ destination := by intro equal; exact neq (congrArg f equal)
        simp only [if_neg xd]
        exact ih parts.2 tailInj hx

end Flapjack.Compiler.Backend.Parmove
