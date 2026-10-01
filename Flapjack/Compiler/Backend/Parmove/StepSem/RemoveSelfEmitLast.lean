import Flapjack.Compiler.Backend.Parmove.Invariants
import Flapjack.Compiler.Backend.Parmove.Permutation
import Flapjack.Compiler.Backend.Parmove.NoRead

namespace Flapjack.Compiler.Backend.Parmove

/-- Generic list reassociation infrastructure, without a separately named HOL
declaration: expose a selected pending move at the parallel list's head. -/
private theorem selectedToFront {α : Type} (before after active : List α) (move : α) :
    ((before ++ [move] ++ after) ++ active).Perm
      (move :: ((before ++ after) ++ active)) := by
  simpa only [List.append_assoc, List.singleton_append, List.cons_append,
    List.nil_append] using
    (List.perm_middle : (before ++ move :: (after ++ active)).Perm
      (move :: (before ++ (after ++ active))))

/-- The RemoveSelf case of HOL's `step_sem`: retain the complete source `wf`
premise and arbitrary emitted history, and conclude equivalence on every real
register. The source constructor is instantiated in the two displayed states. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem_removeSelf {α β : Type} [DecidableEq α]
    (r : Option α) (before after active emitted : List (Move α)) :
    wf (before ++ [(r,r)] ++ after, active, emitted) →
      ∀ env : Option α → β,
        eqenv (sem (before ++ [(r,r)] ++ after, active, emitted) env)
          (sem (before ++ after, active, emitted) env) := by
  intro valid env register _real
  let moves := (before ++ after) ++ active
  let base := seqsem emitted.reverse env
  have perm := selectedToFront before after active (r,r)
  have ordered := (perm.map Prod.fst).nodup_iff.mp valid.1
  have parts : r ∉ moves.map Prod.fst ∧ windmill moves := by
    simpa [moves, windmill] using ordered
  have same := parsem_perm (β := β)
    ((before ++ [(r,r)] ++ after) ++ active) ((r,r) :: moves) ⟨valid.1, perm⟩
  change parsem ((before ++ [(r,r)] ++ after) ++ active) base register =
    parsem moves base register
  rw [same, parsem_cons r r moves base parts.1]
  have unchanged := parsem_untouched base moves r ⟨parts.2, parts.1⟩
  by_cases equal : register = r
  · subst register
    simpa [updateEnv] using unchanged.symm
  · simp [updateEnv, equal]

/-- The EmitLast case of HOL's `step_sem`. The original constructor's NoRead
side condition is expanded literally, and the full input `wf` is retained.
The emitted move is reversed into the end of the sequential history. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem_emitLast {α β : Type} [DecidableEq α]
    (d s : Option α) (pending emitted : List (Move α)) :
    d ∉ pending.map Prod.snd → wf (pending, [(d,s)], emitted) →
      ∀ env : Option α → β,
        eqenv (sem (pending, [(d,s)], emitted) env)
          (sem (pending, [], [(d,s)] ++ emitted) env) := by
  intro noRead valid env register _real
  have perm : (pending ++ [(d,s)]).Perm ((d,s) :: pending) := by
    simp
  have same := parsem_perm (β := β) (pending ++ [(d,s)]) ((d,s) :: pending)
    ⟨valid.1, perm⟩
  change parsem (pending ++ [(d,s)]) (seqsem emitted.reverse env) register =
    parsem (pending ++ []) (seqsem ([(d,s)] ++ emitted).reverse env) register
  rw [same, parsem_NoRead pending d s (seqsem emitted.reverse env) noRead]
  simp only [List.append_nil, List.reverse_append, List.reverse_singleton]
  rw [seqsem_append]
  rfl

end Flapjack.Compiler.Backend.Parmove
