import Flapjack.Compiler.Backend.RegAlloc.ConsideredVar
import Flapjack.Compiler.Backend.RegAlloc.StateFilter
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ArrayRead

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- HOL `st_ex_FILTER_considered_var` (`reg_allocProofScript.sml:2350-2361`).
The HOL statement's free `k` is universally quantified; its existential `fs`
occurs nowhere in the body and, HOL types being inhabited, that vacuous binder
is omitted. The proof reads tags with bounds-checked `getElem`, not the held
HOL `EL` rendering. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_FILTER_considered_var"]
theorem stExFilterConsideredVar :
    ∀ (k : Nat) (ls acc : List Nat) (s : State),
      (∀ x ∈ ls, x < s.node_tag.length) ∧ (∀ x ∈ acc, x < s.node_tag.length) →
      ∃ ts, stExFilter (consideredVar k) ls acc s = (.success ts, s) ∧
        ∀ x ∈ ts, x < s.node_tag.length := by
  intro k ls
  induction ls with
  | nil =>
      intro acc s h
      exact ⟨acc, rfl, h.2⟩
  | cons x xs ih =>
      intro acc s h
      have hx : x < s.node_tag.length := h.1 x (by simp)
      have hxs : ∀ y ∈ xs, y < s.node_tag.length := fun y hy => h.1 y (by simp [hy])
      have hsub : nodeTagSub x s = (.success s.node_tag[x], s) := by
        simp only [nodeTagSub, arraySub, mSub_success_getElem _ _ _ hx]
      obtain ⟨b, hb⟩ : ∃ b, consideredVar k x s = (.success b, s) := by
        refine ⟨decide (s.node_tag[x] = .Atemp) ||
          (match s.node_tag[x] with
            | .Fixed n => decide (n < k)
            | _ => false), ?_⟩
        simp only [consideredVar, isAtemp, isFixedK, Translator.Monadic.MonadBase.bind,
          Translator.Monadic.MonadBase.ret, hsub]
        rfl
      cases b with
      | true =>
          obtain ⟨ts, heq, hts⟩ := ih (x :: acc) s ⟨hxs, by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact h.2 y hy⟩
          refine ⟨ts, ?_, hts⟩
          simp only [stExFilter, Translator.Monadic.MonadBase.bind, hb, if_true]
          exact heq
      | false =>
          obtain ⟨ts, heq, hts⟩ := ih acc s ⟨hxs, h.2⟩
          refine ⟨ts, ?_, hts⟩
          simp only [stExFilter, Translator.Monadic.MonadBase.bind, hb, Bool.false_eq_true,
            if_false]
          exact heq

end Flapjack.RegAlloc
