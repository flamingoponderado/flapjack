import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Motive

/-!
# `max_depth_call_graph_lemma`: `Seq` case
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

namespace CallGraphLemmaSeqWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaSeqWitnesses

open CallGraphLemmaSeqWitnesses

/-- `option_le` arithmetic for the `Seq` composition (Flapjack infrastructure):
the second run's bound, taken from the first run's final `stack_max`, stays
below the `Branch` bound. -/
theorem seq_bound (m ss g d1 d2 m1 m2 : Option Nat)
    (h1 : optionLe m1 (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g d1))))
    (h2 : optionLe m2 (optionMap₂ max m1 (optionMap₂ (· + ·) ss (optionMap₂ max g d2)))) :
    optionLe m2 (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g (optionMap₂ max d1 d2)))) := by
  rcases m with _ | m <;> rcases ss with _ | ss <;> rcases g with _ | g <;>
    rcases d1 with _ | d1 <;> rcases d2 with _ | d2 <;>
    rcases m1 with _ | m1 <;> rcases m2 with _ | m2 <;>
    simp only [optionMap₂, optionLe] at h1 h2 ⊢
  all_goals omega

/-- `option_le` monotonicity for a run stopping in the first statement
(Flapjack infrastructure). -/
theorem seq_bound_left (m ss g d1 d2 m1 : Option Nat)
    (h1 : optionLe m1 (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g d1)))) :
    optionLe m1 (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g (optionMap₂ max d1 d2)))) := by
  rcases m with _ | m <;> rcases ss with _ | ss <;> rcases g with _ | g <;>
    rcases d1 with _ | d1 <;> rcases d2 with _ | d2 <;> rcases m1 with _ | m1 <;>
    simp only [optionMap₂, optionLe] at h1 ⊢
  all_goals omega

/-- `max_depth_call_graph_lemma`, `Seq` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Seq {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (ih : (∀ res s1, (res, s1) = evaluate c1 s ∧ res = none → depthPost c2 s1) ∧
      depthPost c1 s) :
    depthPost (.seq c1 c2) s := by
  obtain ⟨ih2, ih1⟩ := ih
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  rcases h1 : evaluate c1 s with ⟨r1, s1⟩
  have hunfold : ∀ r, evaluate c1 s = (some r, s1) → evaluate (.seq c1 c2) s = (some r, s1) := by
    intro r h
    rw [evaluate, fix_clock_evaluate]
    split
    rename_i heq
    rw [h] at heq
    cases heq
    rfl
  have hunfoldNone : evaluate c1 s = (none, s1) → evaluate (.seq c1 c2) s = evaluate c2 s1 := by
    intro h
    rw [evaluate, fix_clock_evaluate]
    split
    rename_i heq
    rw [h] at heq
    cases heq
    rfl
  simp only [callGraph, maxDepth_mkBranch, maxDepth]
  cases r1 with
  | some r =>
      rw [hunfold r h1] at herr ⊢
      have herr1 : (evaluate c1 s).1 ≠ some .error := by rw [h1]; exact herr
      have p1 := ih1 funs n ns funs2 ⟨hsub, hcode, hloc, herr1, hmem, hnd, hdom⟩
      rw [h1] at p1
      refine ⟨seq_bound_left _ _ _ _ _ _ p1.1, fun hne => ?_⟩
      have hd1 : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) c1) ≠ none := by
        intro h; apply hne.2; rw [h]; rfl
      exact p1.2 ⟨hne.1, hd1⟩
  | none =>
      rw [hunfoldNone h1] at herr ⊢
      have herr1 : (evaluate c1 s).1 ≠ some .error := by rw [h1]; simp
      have p1 := ih1 funs n ns funs2 ⟨hsub, hcode, hloc, herr1, hmem, hnd, hdom⟩
      rw [h1] at p1
      dsimp only at p1
      -- if any of the three bounds is `NONE` the conclusion is immediate
      by_cases hg : maxDepthGraphs s.stackSize ns ns funs funs2 = none
      · refine ⟨?_, fun hne => absurd hg hne.1⟩
        rw [hg]; simp [optionMap₂, optionLe]
      by_cases hd1 : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) c1) = none
      · refine ⟨?_, fun hne => absurd (by rw [hd1]; rfl) hne.2⟩
        rw [hd1]; simp [optionMap₂, optionLe]
      obtain ⟨hss1, hls1⟩ := p1.2 ⟨hg, hd1⟩
      have hls1' := hls1 (Or.inl rfl)
      have hstack : wordSemStackSize s1.stack = wordSemStackSize s.stack :=
        WordSemStackEq.evaluate_NONE_stack_size_const c1 s s1 h1
      have hcode1 : sptSubspt s.code s1.code := evaluate_code_only_grows c1 s none s1 h1
      have p2 := ih2 none s1 ⟨h1.symm, rfl⟩ funs n ns funs2
        ⟨hsub, sptSubsptTrans _ _ _ ⟨hcode, hcode1⟩, by rw [hls1', hss1]; exact hloc,
          herr, hmem, hnd, hdom⟩
      rw [hss1, hstack] at p2
      refine ⟨seq_bound _ _ _ _ _ _ _ p1.1 p2.1, fun hne => ?_⟩
      have hd2 : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) c2) ≠ none := by
        intro h; apply hne.2; rw [h, optionMap2_none_right]
      obtain ⟨hss2, hls2⟩ := p2.2 ⟨hne.1, hd2⟩
      exact ⟨hss2, fun h => (hls2 h).trans hls1'⟩

end Flapjack.Compiler.Backend.WordDepthProof
