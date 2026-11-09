module

public import Flapjack.Compiler.Backend.Parmove.Steps
public import Flapjack.Compiler.Backend.Parmove.Invariants.Path

@[expose] public section

namespace Flapjack.Compiler.Backend.Parmove

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_step"]
theorem wf_step {α : Type} (first second : State α) :
    Step first second → wf first → wf second := by
  intro step valid
  cases step with
  | removeSelf r before after active emitted =>
      simp only [wf, windmill, List.map_append, List.nodup_append, List.mem_append,
        List.append_assoc, List.cons_append, List.nil_append] at valid ⊢
      grind
  | start d s before after emitted =>
      simp only [wf, windmill, path, List.map_append, List.nodup_append, List.mem_append,
        List.append_assoc, List.cons_append, List.nil_append] at valid ⊢
      grind
  | extend d r s before after active emitted =>
      simp only [wf, windmill, path, List.map_append, List.nodup_append, List.mem_append,
        List.append_assoc, List.cons_append, List.nil_append] at valid ⊢
      grind
  | save d s pending active emitted =>
      simp only [wf, windmill] at valid ⊢
      rcases valid with ⟨unique, pd, ps, front, ad, oldPath⟩
      refine ⟨?_, pd, ps, ?_, ?_, path_change_start active (d, none) (d, s) ⟨oldPath, rfl⟩⟩
      · grind
      · intro _ move member
        apply front (by simp) move
        simpa using member
      · intro move member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact ad move (by simp [member])
        · exact ad (d,s) (by simp)
  | emitHead d0 dn s0 sn pending active emitted noRead distinct =>
      simp only [wf, windmill] at valid ⊢
      rcases valid with ⟨unique, pd, ps, front, ad, oldPath⟩
      refine ⟨?_, pd, ps, ?_, ?_, path_tail (active ++ [(d0,s0)]) (dn,sn) oldPath⟩
      · grind
      · intro _ move member
        apply front (by simp) move
        simpa only [← List.cons_append, List.dropLast_concat, List.singleton_append, List.mem_cons] using
          (Or.inr (by simpa using member) : move = (dn,sn) ∨ move ∈ active)
      · intro move member
        exact ad move (List.mem_cons.mpr (Or.inr member))
  | emitLast d s pending emitted noRead =>
      simp only [wf, windmill, path, List.map_append, List.nodup_append] at valid ⊢
      grind

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_steps"]
theorem wf_steps {α : Type} (first second : State α) :
    wf first ∧ Steps first second → wf second := by
  rintro ⟨valid, steps⟩
  induction steps with
  | refl => exact valid
  | @tail middle last steps step ih => exact wf_step middle last step ih

end Flapjack.Compiler.Backend.Parmove
