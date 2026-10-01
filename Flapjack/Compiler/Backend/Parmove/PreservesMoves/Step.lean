import Flapjack.Compiler.Backend.Parmove.Steps
import Flapjack.Compiler.Backend.Parmove.StateToList

namespace Flapjack.Compiler.Backend.Parmove

/-- Full primitive-step destination preservation. The existential source may
change when a cycle is saved through the scratch register. The original
non-self premise is retained; no state validity or scratch-safety premise is
needed. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_preserves_moves"]
theorem stepPreservesMoves {α : Type} (first second : State α) :
    Step first second →
    ∀ x, (∃ y, (x, y) ∈ stateToList first ∧ x ≠ y) →
      ∃ y, (x, y) ∈ stateToList second ∧ x ≠ y := by
  intro transition x witness
  cases transition with
  | save d s pending active emitted =>
      obtain ⟨y, member, nonself⟩ := witness
      simp only [stateToList, List.mem_append, List.mem_cons, List.not_mem_nil,
        Prod.mk.injEq, or_assoc, or_false] at member ⊢
      rcases member with hp | ha | saved | he
      · exact ⟨y, Or.inl hp, nonself⟩
      · exact ⟨y, Or.inr (Or.inl ha), nonself⟩
      · obtain ⟨rfl, rfl⟩ := saved
        by_cases scratch : x = none
        · subst x
          exact ⟨y, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), nonself⟩
        · exact ⟨none, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), scratch⟩
      · exact ⟨y, Or.inr (Or.inr (Or.inr (Or.inr he))), nonself⟩
  | _ =>
      simp_all [stateToList, List.mem_append, List.mem_cons] <;> grind

end Flapjack.Compiler.Backend.Parmove
