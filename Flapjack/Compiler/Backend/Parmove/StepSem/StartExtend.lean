import Flapjack.Compiler.Backend.Parmove.Invariants
import Flapjack.Compiler.Backend.Parmove.Permutation

namespace Flapjack.Compiler.Backend.Parmove

/-- Generic list reassociation for moving a selected pending move to the active
head. This is infrastructure, not a separately named HOL declaration. -/
private theorem pendingToActive {α : Type} (before after active : List α) (move : α) :
    ((before ++ [move] ++ after) ++ active).Perm
      ((before ++ after) ++ move :: active) := by
  apply List.Perm.trans (l₂ := move :: (before ++ after ++ active))
  · simpa only [List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using
      (List.perm_middle : (before ++ move :: (after ++ active)).Perm
        (move :: (before ++ (after ++ active))))
  · exact (List.perm_middle : ((before ++ after) ++ move :: active).Perm
      (move :: ((before ++ after) ++ active))).symm

/-- The Start case of HOL's six-clause `step_sem` proof. The input invariant
and whole environment-equivalence conclusion are retained; the constructor
itself is instantiated, so no separate Step premise is needed. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem_start {α β : Type} [DecidableEq α]
    (d s : Option α) (before after emitted : List (Move α)) :
    wf (before ++ [(d,s)] ++ after, [], emitted) →
      ∀ env : Option α → β,
        eqenv (sem (before ++ [(d,s)] ++ after, [], emitted) env)
          (sem (before ++ after, [(d,s)], emitted) env) := by
  intro valid env register _real
  have same := parsem_perm (β := β)
    ((before ++ [(d,s)] ++ after) ++ [])
    ((before ++ after) ++ (d,s) :: [])
    ⟨valid.1, pendingToActive before after [] (d,s)⟩
  exact congrFun (congrFun same (seqsem emitted.reverse env)) register

/-- The Extend case of HOL's `step_sem` proof. The active path is kept in the
input state, without replacing the original invariant by a stronger premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem_extend {α β : Type} [DecidableEq α]
    (d r s : Option α) (before after active emitted : List (Move α)) :
    wf (before ++ [(r,d)] ++ after, [(d,s)] ++ active, emitted) →
      ∀ env : Option α → β,
        eqenv (sem (before ++ [(r,d)] ++ after, [(d,s)] ++ active, emitted) env)
          (sem (before ++ after, [(r,d),(d,s)] ++ active, emitted) env) := by
  intro valid env register _real
  have same := parsem_perm (β := β)
    ((before ++ [(r,d)] ++ after) ++ ((d,s) :: active))
    ((before ++ after) ++ (r,d) :: (d,s) :: active)
    ⟨valid.1, pendingToActive before after ((d,s) :: active) (r,d)⟩
  exact congrFun (congrFun same (seqsem emitted.reverse env)) register

end Flapjack.Compiler.Backend.Parmove
