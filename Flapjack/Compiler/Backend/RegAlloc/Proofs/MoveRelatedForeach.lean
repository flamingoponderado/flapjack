import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
import Flapjack.Compiler.Backend.RegAlloc.StateForeach

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- HOL `st_ex_FOREACH_update_move_related` (`reg_allocProofScript.sml:2645-2656`):
setting the move flag of in-range nodes succeeds, changes only `move_related`
and preserves its length. HOL `EVERY` is a bounded `∀`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_FOREACH_update_move_related"]
theorem stExForeachUpdateMoveRelated :
    ∀ (ls : List Nat) (s : State) (b : Bool),
      (∀ v ∈ ls, v < s.move_related.length) →
      ∃ lss, stExForeach ls (fun x => updateMoveRelated x b) s =
          (.success (), { s with move_related := lss }) ∧
        lss.length = s.move_related.length := by
  intro ls
  induction ls with
  | nil => intro s b _; exact ⟨s.move_related, rfl, rfl⟩
  | cons h t ih =>
      intro s b hb
      have hh : h < s.move_related.length := hb h (by simp)
      let s' : State := { s with move_related := s.move_related.set h b }
      have ht : ∀ v ∈ t, v < s'.move_related.length := by
        intro v hv; simpa [s'] using hb v (by simp [hv])
      obtain ⟨lss, heq, hlen⟩ := ih s' b ht
      refine ⟨lss, ?_, by simpa [s'] using hlen⟩
      simp only [stExForeach, ignoreBind, updateMoveRelatedEqn, hh, if_true]
      rw [heq]
