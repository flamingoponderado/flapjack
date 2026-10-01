import Flapjack.Compiler.Backend.Parmove.Steps
import Flapjack.Compiler.Backend.Parmove.Invariants.Path

namespace Flapjack.Compiler.Backend.Parmove

/-- Generic list reassociation infrastructure, not a named HOL declaration. -/
private theorem moveAcross {α : Type} (before after tail : List α) (move : α) :
    ((before ++ [move] ++ after) ++ tail).Perm ((before ++ after) ++ move :: tail) := by
  apply List.Perm.trans (l₂ := move :: (before ++ after ++ tail))
  · simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      (List.perm_middle : (before ++ move :: (after ++ tail)).Perm (move :: (before ++ (after ++ tail))))
  · exact (List.perm_middle : ((before ++ after) ++ move :: tail).Perm
      (move :: ((before ++ after) ++ tail))).symm

/-- Generic list-deletion infrastructure, not a named HOL declaration. -/
private theorem removeMove {α : Type} (before after tail : List α) (move : α) :
    ((before ++ after) ++ tail).Sublist ((before ++ [move] ++ after) ++ tail) := by
  simpa only [List.append_assoc] using
    ((List.sublist_append_right [move] after).append_left before).append_right tail

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_step"]
theorem wf_step {α : Type} (first second : State α) :
    Step first second → wf first → wf second := by
  intro step valid
  cases step with
  | removeSelf r before after active emitted =>
      simp only [wf] at valid ⊢
      rcases valid with ⟨unique, pd, ps, front, ad, oldPath⟩
      refine ⟨?_, ?_, ?_, front, ad, oldPath⟩
      · exact ((removeMove before after active (r,r)).map Prod.fst).nodup unique
      · intro move member
        apply pd move
        simpa using ((removeMove before after [] (r,r)).subset (by simpa using member))
      · intro move member
        apply ps move
        simpa using ((removeMove before after [] (r,r)).subset (by simpa using member))
  | start d s before after emitted =>
      simp only [wf] at valid ⊢
      rcases valid with ⟨unique, pd, ps, _, _, _⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, by simp [path]⟩
      · simpa [windmill] using ((moveAcross before after [] (d,s)).map Prod.fst).nodup_iff.mp unique
      · intro move member
        apply pd move
        simpa using ((removeMove before after [] (d,s)).subset (by simpa using member))
      · intro move member
        apply ps move
        simpa using ((removeMove before after [] (d,s)).subset (by simpa using member))
      · simp
      · intro move member
        have same : move = (d,s) := by simpa using member
        subst move
        exact pd (d,s) (by simp)
  | extend d r s before after active emitted =>
      simp only [wf] at valid ⊢
      rcases valid with ⟨unique, pd, ps, front, ad, oldPath⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ((moveAcross before after ((d,s)::active) (r,d)).map Prod.fst).nodup_iff.mp unique
      · intro move member
        apply pd move
        simpa using ((removeMove before after [] (r,d)).subset (by simpa using member))
      · intro move member
        apply ps move
        simpa using ((removeMove before after [] (r,d)).subset (by simpa using member))
      · intro _ move member
        change move ∈ ((r,d) :: (d,s) :: active).dropLast at member
        rw [List.dropLast_cons_of_ne_nil (show ((d,s)::active) ≠ [] from by simp)] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact ad (d,s) (by simp)
        · exact front (by simp) move member
      · intro move member
        rcases List.mem_cons.mp member with rfl | member
        · exact pd (r,d) (by simp)
        · exact ad move member
      · simpa [path] using oldPath
  | save d s pending active emitted =>
      simp only [wf] at valid ⊢
      rcases valid with ⟨unique, pd, ps, front, ad, oldPath⟩
      refine ⟨?_, pd, ps, ?_, ?_, path_change_start active (d, none) (d, s) ⟨oldPath, rfl⟩⟩
      · simpa [windmill] using unique
      · intro _ move member
        apply front (by simp) move
        simpa using member
      · intro move member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact ad move (by simp [member])
        · exact ad (d,s) (by simp)
  | emitHead d0 dn s0 sn pending active emitted noRead distinct =>
      simp only [wf] at valid ⊢
      rcases valid with ⟨unique, pd, ps, front, ad, oldPath⟩
      refine ⟨?_, pd, ps, ?_, ?_, path_tail (active ++ [(d0,s0)]) (dn,sn) oldPath⟩
      · have sub : (pending ++ (active ++ [(d0,s0)])).Sublist
            (pending ++ ((dn,sn) :: (active ++ [(d0,s0)]))) := by
          have tailSub : (active ++ [(d0,s0)]).Sublist ((dn,sn) :: (active ++ [(d0,s0)])) := by
            simp
          exact tailSub.append_left pending
        exact (sub.map Prod.fst).nodup unique
      · intro _ move member
        apply front (by simp) move
        simpa only [← List.cons_append, List.dropLast_concat, List.singleton_append, List.mem_cons] using
          (Or.inr (by simpa using member) : move = (dn,sn) ∨ move ∈ active)
      · intro move member
        exact ad move (List.mem_cons.mpr (Or.inr member))
  | emitLast d s pending emitted noRead =>
      simp only [wf] at valid ⊢
      rcases valid with ⟨unique, pd, ps, _, _, _⟩
      refine ⟨?_, pd, ps, ?_, ?_, by simp [path]⟩
      · simpa [windmill] using ((List.sublist_append_left pending [(d,s)]).map Prod.fst).nodup unique
      · simp
      · simp

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_steps"]
theorem wf_steps {α : Type} (first second : State α) :
    wf first ∧ Steps first second → wf second := by
  rintro ⟨valid, steps⟩
  induction steps with
  | refl => exact valid
  | @tail middle last steps step ih => exact wf_step middle last step ih

end Flapjack.Compiler.Backend.Parmove
