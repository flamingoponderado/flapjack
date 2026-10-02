import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
import Flapjack.Misc.ListEl

/-! Full native get_vars helper for SSA reconciliation, counterpart of the
local lemma at word_allocProofScript.sml:6524–6549. The HOL tree maps remain
Spt, THE/EL retain their unspecified out-of-domain values, and the original
premises prove existence of the complete returned list rather than assuming it.
-/
namespace Flapjack.Compiler.Backend.WordAlloc

namespace SSAReconcileGetVarsWitness
/-- Canonical imported native WordSem carrier roundtrip, not a HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end SSAReconcileGetVarsWitness

/-- HOL's full reconciliation read lemma: distinct source names and native
lookup existence yield the result list, its exact length and every indexed
lookup. fpRegs/store use the canonical finite-support state representation;
locals and curSsa retain literal HOL num_map trees. Positive BitVec width
and universe-zero native code/FFI host carriers implement the standard word
translation. No successful getVars result, SSA simulation or locals relation
is assumed. The distinctness premise is retained even though list induction
also proves the result without it. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_get_vars_lemma"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem ssaReconcileGetVarsLemma {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ls : List Nat) (curSsa : Spt Nat) (cst : WordSemStateFiniteExact width C F),
      ls.Nodup ∧
        (∀ v, v ∈ ls → ∃ value,
          sptLookup (holThe (sptLookup v curSsa)) cst.locals = some value) →
      ∃ vs, WordSemStateFiniteExact.getVars
          (ls.map (fun v => holThe (sptLookup v curSsa))) cst = some vs ∧
        vs.length = ls.length ∧
        ∀ i, i < ls.length →
          sptLookup (holThe (sptLookup (holEl i ls) curSsa)) cst.locals =
            some (holEl i vs) := by
  intro ls
  induction ls with
  | nil =>
      intro curSsa cst _
      exact ⟨[], rfl, rfl, by simp⟩
  | cons name names ih =>
      intro curSsa cst h
      obtain ⟨values, read, length, indexed⟩ := ih curSsa cst
        ⟨(List.nodup_cons.mp h.1).2, fun v hv => h.2 v (by simp [hv])⟩
      obtain ⟨value, headRead⟩ := h.2 name (by simp)
      refine ⟨value :: values, ?_, by simp [length], ?_⟩
      · simp [List.map_cons, WordSemStateFiniteExact.getVars,
          WordSemStateFiniteExact.getVar, headRead, read]
      · intro i bound
        cases i with
        | zero => simpa [holEl, holHd] using headRead
        | succ i =>
            simpa [holEl, List.tail_cons] using indexed i (by simpa using bound)

end Flapjack.Compiler.Backend.WordAlloc
