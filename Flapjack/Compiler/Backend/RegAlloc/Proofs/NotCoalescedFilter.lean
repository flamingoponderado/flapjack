import Flapjack.Compiler.Backend.RegAlloc.SplitDegree
import Flapjack.Compiler.Backend.RegAlloc.StateFilter
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ArrayRead

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- HOL `st_ex_FILTER_is_not_coalesced` (`reg_allocProofScript.sml:2286-2298`):
filtering in-range nodes (with an in-range accumulator) by `is_not_coalesced`
succeeds without changing the state and returns in-range nodes. HOL `EVERY` is
a bounded `∀`. The HOL statement also binds an existential `fs` that occurs
nowhere in its body; since every HOL type is inhabited that binder is vacuous
and is omitted. The proof reads elements with bounds-checked `getElem`, not the
held HOL `EL` rendering. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_FILTER_is_not_coalesced"]
theorem stExFilterIsNotCoalesced :
    ∀ (ls acc : List Nat) (s : State),
      (∀ x ∈ ls, x < s.coalesced.length) ∧ (∀ x ∈ acc, x < s.coalesced.length) →
      ∃ ts, stExFilter isNotCoalesced ls acc s = (.success ts, s) ∧
        ∀ x ∈ ts, x < s.coalesced.length := by
  intro ls
  induction ls with
  | nil =>
      intro acc s h
      exact ⟨acc, rfl, h.2⟩
  | cons x xs ih =>
      intro acc s h
      have hx : x < s.coalesced.length := h.1 x (by simp)
      have hxs : ∀ y ∈ xs, y < s.coalesced.length := fun y hy => h.1 y (by simp [hy])
      have hsub : isNotCoalesced x s = (.success (decide (x = s.coalesced[x])), s) := by
        simp only [isNotCoalesced, Translator.Monadic.MonadBase.bind, coalescedSub, arraySub,
          mSub_success_getElem _ _ _ hx]
        rfl
      by_cases hc : x = s.coalesced[x]
      · obtain ⟨ts, heq, hts⟩ := ih (x :: acc) s ⟨hxs, by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact h.2 y hy⟩
        refine ⟨ts, ?_, hts⟩
        have hsub' : isNotCoalesced x s = (.success true, s) := by
          rw [hsub, decide_eq_true hc]
        simp only [stExFilter, Translator.Monadic.MonadBase.bind, hsub', if_true]
        exact heq
      · obtain ⟨ts, heq, hts⟩ := ih acc s ⟨hxs, h.2⟩
        refine ⟨ts, ?_, hts⟩
        have hsub' : isNotCoalesced x s = (.success false, s) := by
          rw [hsub, decide_eq_false hc]
        simp only [stExFilter, Translator.Monadic.MonadBase.bind, hsub', Bool.false_eq_true,
          if_false]
        exact heq

end Flapjack.RegAlloc
