import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Seq

/-!
# `max_depth_call_graph_lemma`: `If` and `MustTerminate` cases
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

namespace CallGraphLemmaIfWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaIfWitnesses

open CallGraphLemmaIfWitnesses

/-- `option_le` monotonicity for the second branch (Flapjack infrastructure). -/
theorem seq_bound_right (m ss g d1 d2 m1 : Option Nat)
    (h1 : optionLe m1 (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g d2)))) :
    optionLe m1 (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g (optionMap₂ max d1 d2)))) := by
  rcases m with _ | m <;> rcases ss with _ | ss <;> rcases g with _ | g <;>
    rcases d1 with _ | d1 <;> rcases d2 with _ | d2 <;> rcases m1 with _ | m1 <;>
    simp only [optionMap₂, optionLe] at h1 ⊢
  all_goals omega

/-- `max_depth_call_graph_lemma`, `If` case. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallGraphLemma_If {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width))
    (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (ih : (∀ v3 v4 x y v, (WordSemStateFiniteExact.getVar r1 s,
          WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ v = true → depthPost c1 s) ∧
      (∀ v3 v4 x y v, (WordSemStateFiniteExact.getVar r1 s,
          WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ ¬ v = true → depthPost c2 s)) :
    depthPost (.ite cmp r1 ri c1 c2) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  simp only [callGraph, maxDepth_mkBranch, maxDepth]
  rcases hx : WordSemStateFiniteExact.getVar r1 s with _ | x
  · exact absurd (by rw [evaluate, hx]) herr
  rcases hy : WordSemStateFiniteExact.getVarImm ri s with _ | y
  · exact absurd (by rw [evaluate, hx, hy]) herr
  rcases hc : wordSemWordCmp cmp x y with _ | b
  · exact absurd (by rw [evaluate, hx, hy]; simp only [hc]) herr
  cases b with
  | true =>
      have hev : evaluate (.ite cmp r1 ri c1 c2) s = evaluate c1 s := by
        rw [evaluate, hx, hy]; simp only [hc]
      rw [hev] at herr ⊢
      have p := ih.1 (some x) (some y) x y true ⟨by rw [hx, hy], rfl, rfl, hc, rfl⟩
        funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
      refine ⟨seq_bound_left _ _ _ _ _ _ p.1, fun hne => p.2 ⟨hne.1, fun h => hne.2 ?_⟩⟩
      rw [h]; rfl
  | false =>
      have hev : evaluate (.ite cmp r1 ri c1 c2) s = evaluate c2 s := by
        rw [evaluate, hx, hy]; simp only [hc]
      rw [hev] at herr ⊢
      have p := ih.2 (some x) (some y) x y false
        ⟨by rw [hx, hy], rfl, rfl, hc, Bool.false_ne_true⟩
        funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
      refine ⟨seq_bound_right _ _ _ _ _ _ p.1, fun hne => p.2 ⟨hne.1, fun h => hne.2 ?_⟩⟩
      rw [h, optionMap2_none_right]

/-- `max_depth_call_graph_lemma`, `MustTerminate` case: the body runs on the
same stack fields with only `clock`/`termdep` changed. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallGraphLemma_MustTerminate {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (ih : s.termdep ≠ 0 →
      depthPost p { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }) :
    depthPost (.mustTerminate p) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  simp only [callGraph]
  by_cases hd : s.termdep = 0
  · exact absurd (by rw [evaluate, dif_pos hd]) herr
  rcases he : evaluate p { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } with ⟨r, s1⟩
  have hTO : r = some .timeOut → evaluate (.mustTerminate p) s = (some .error, s) := by
    intro hr
    rw [evaluate, dif_neg hd]
    split
    rename_i heq
    rw [he] at heq
    cases heq
    subst hr
    rfl
  have hnt : r ≠ some .timeOut := fun hr => herr (by rw [hTO hr])
  have hev : evaluate (.mustTerminate p) s = (r, { s1 with clock := s.clock, termdep := s.termdep }) := by
    rw [evaluate, dif_neg hd]
    split
    rename_i heq
    rw [he] at heq
    cases heq
    split
    · exact absurd rfl hnt
    · rfl
  rw [hev] at herr ⊢
  have herr' : (evaluate p { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }).1 ≠ some .error := by rw [he]; exact herr
  have q := ih hd funs n ns funs2 ⟨hsub, hcode, hloc, herr', hmem, hnd, hdom⟩
  rw [he] at q
  exact q

end Flapjack.Compiler.Backend.WordDepthProof
