import Flapjack.Compiler.Backend.Parmove.Invariants.Path
import Flapjack.Compiler.Backend.Parmove.Permutation
import Flapjack.Compiler.Backend.Parmove.NoRead

namespace Flapjack.Compiler.Backend.Parmove

/-- Genuine EmitHead case: full wf and both original constructor conditions.
The remaining path no-read fact is derived, not an extra semantic premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem_emitHead {α β : Type} [DecidableEq α]
    (d0 dn s0 sn : Option α) (pending active emitted : List (Move α)) :
    dn ∉ pending.map Prod.snd → dn ≠ s0 →
    wf (pending, [(dn,sn)] ++ active ++ [(d0,s0)], emitted) →
      ∀ env : Option α → β,
        eqenv (sem (pending, [(dn,sn)] ++ active ++ [(d0,s0)], emitted) env)
          (sem (pending, active ++ [(d0,s0)], [(dn,sn)] ++ emitted) env) := by
  intro noRead different valid env register _real
  have activeUnique : windmill ((dn,sn) :: (active ++ [(d0,s0)])) := by
    have full : (pending.map Prod.fst ++
        ([(dn,sn)] ++ active ++ [(d0,s0)]).map Prod.fst).Nodup := by
      simpa [windmill] using valid.1
    have suffix := (List.nodup_append.mp full).2.1
    simpa [windmill, List.append_assoc] using suffix
  have activePath : path ((dn,sn) :: (active ++ [(d0,s0)])) := by
    simpa using valid.2.2.2.2.2
  have tailNoRead := path_tail_noRead (dn,sn) active (d0,s0)
    activePath activeUnique different
  have remainingNoRead : dn ∉ (pending ++ (active ++ [(d0,s0)])).map Prod.snd := by
    simpa only [List.map_append, List.mem_append, not_or] using
      And.intro noRead tailNoRead
  have perm : (pending ++ ([(dn,sn)] ++ active ++ [(d0,s0)])).Perm
      ((dn,sn) :: (pending ++ (active ++ [(d0,s0)]))) := by
    simpa only [List.singleton_append, List.cons_append, List.nil_append] using
      (List.perm_middle : (pending ++ (dn,sn) :: (active ++ [(d0,s0)])).Perm
        ((dn,sn) :: (pending ++ (active ++ [(d0,s0)]))))
  have same := parsem_perm (β := β) _ _ ⟨valid.1, perm⟩
  change parsem (pending ++ ([(dn,sn)] ++ active ++ [(d0,s0)]))
      (seqsem emitted.reverse env) register =
    parsem (pending ++ (active ++ [(d0,s0)]))
      (seqsem ([(dn,sn)] ++ emitted).reverse env) register
  rw [same, parsem_NoRead _ dn sn _ remainingNoRead]
  simp only [List.reverse_append, List.reverse_singleton]
  rw [seqsem_append]
  rfl

end Flapjack.Compiler.Backend.Parmove
