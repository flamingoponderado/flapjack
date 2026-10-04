import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.CallUnfold

/-!
# `max_depth_call_graph_lemma`: tail-call part of the `Call` case

`ret = NONE`. As in HOL: a destination already on `ns` has graph `Leaf`, and
the callee's depth is bounded through `MEM_max_depth_graphs`; a fresh callee
recurses with `d :: ns`, the `LENGTH ns < size funs2` guard holding by
`LENGTH_LESS_size`, and the extended graph set is bounded by
`option_le_max_depth_graphs`.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

/-- Conclusion when the call graph's depth is `NONE` (Flapjack infrastructure). -/
theorem post_of_graph_none {m' m ss g x : Option Nat} {P : Prop}
    (hx : x = none) :
    optionLe m' (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g x))) ∧
      (g ≠ none ∧ x ≠ none → P) := by
  subst hx
  refine ⟨?_, fun h => absurd rfl h.2⟩
  rw [optionMap2_none_right, optionMap2_none_right, optionMap2_none_right]
  trivial

/-- Arithmetic of the `MEM` tail call (Flapjack infrastructure). -/
theorem tail_mem_bound (m sz ld g d t : Option Nat)
    (h1 : optionLe t (optionMap₂ max (wordSemOptionMax m (wordSemOptionAdd sz ld))
      (optionMap₂ (· + ·) sz (optionMap₂ max g d))))
    (h2 : optionLe (optionMap₂ max ld (optionMap₂ max d (some 0))) g) :
    optionLe t (optionMap₂ max m (optionMap₂ (· + ·) sz (optionMap₂ max g (some 0)))) := by
  rcases m with _ | m <;> rcases sz with _ | sz <;> rcases ld with _ | ld <;>
    rcases g with _ | g <;> rcases d with _ | d <;> rcases t with _ | t <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe] at h1 h2 ⊢
  all_goals omega

/-- Arithmetic of the fresh tail call (Flapjack infrastructure). -/
theorem tail_fresh_bound (m sz ld g g2 d t : Option Nat)
    (h1 : optionLe t (optionMap₂ max (wordSemOptionMax m (wordSemOptionAdd sz ld))
      (optionMap₂ (· + ·) sz (optionMap₂ max (optionMap₂ max ld (optionMap₂ max d g2)) d))))
    (h2 : optionLe g2 g) :
    optionLe t (optionMap₂ max m (optionMap₂ (· + ·) sz
      (optionMap₂ max g (optionMap₂ max (optionMap₂ (· + ·) ld (some 0)) d)))) := by
  rcases m with _ | m <;> rcases sz with _ | sz <;> rcases ld with _ | ld <;>
    rcases g with _ | g <;> rcases g2 with _ | g2 <;> rcases d with _ | d <;>
    rcases t with _ | t <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe] at h1 h2 ⊢
  all_goals omega

/-- The tail-call (`ret = NONE`) part of the `Call` case, from the evaluator's
tail-call induction hypothesis (Flapjack infrastructure; the tagged `Call` case
assembles it). -/
theorem depthPost_call_tail {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (htail : ∀ xs v3 args1 v10 prog ss,
      WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc none xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧
        (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
          = none ∧ handler = none ∧ s.clock ≠ 0 →
      depthPost prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))) :
    depthPost (.call none dest args handler) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- a missing destination has an `Unknown` graph
  rcases dest with _ | d
  · exact post_of_graph_none (by simp [callGraph, maxDepth])
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · exact absurd (by rw [ht]; simp only [hg]) herr
  have hbad : ¬ wordSemBadDestArgs (some d) args = true := by simp [wordSemBadDestArgs]
  rcases hf : wordSemFindCode (some d) (wordSemAddRetLoc none xs) s.code s.stackSize with
    _ | ⟨args1, prog, ss⟩
  · exact absurd (by rw [ht]; simp only [hg, hbad, Bool.false_eq_true, if_false, hf]) herr
  obtain ⟨⟨a, hcd⟩, hss, hargs⟩ := findCode_some_dest hf
  subst hss
  rcases handler with _ | hh
  swap
  · exact absurd (by rw [ht]; simp only [hg, hbad, Bool.false_eq_true, if_false, hf]) herr
  by_cases hz : s.clock = 0
  · -- `TimeOut` after flushing: no stack change
    have hev : evaluate (.call none (some d) args none) s = (some .timeOut, flushState true s) := by
      rw [ht]; simp only [hg, hbad, Bool.false_eq_true, hf, hz, ↓reduceIte]
    rw [hev]
    exact ⟨(optionLe_X_MAX_X _ _).2, fun _ => ⟨rfl, fun h => by simp at h⟩⟩
  have hev := evaluate_call_tail hg hbad hf hz
  rcases hr : evaluate prog
      (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize) (decClock s)) with ⟨r, t⟩
  rw [hr] at hev
  rw [hev] at herr ⊢
  have hgood : wordSemBadFunReturn r = false := by
    by_contra hb
    simp only [Bool.not_eq_false] at hb
    simp [hb] at herr
  simp only [hgood, Bool.false_eq_true, if_false] at herr ⊢
  have hloc_vac : ¬ (r = none ∨ (∃ k, r = some (.break k)) ∨ ∃ k, r = some (.continue k)) := by
    rintro (rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩) <;> simp [wordSemBadFunReturn] at hgood
  have hIH := htail xs (args1, prog, sptLookup d s.stackSize) args1
    (prog, sptLookup d s.stackSize) prog (sptLookup d s.stackSize)
    ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, hz⟩
  have hcenv_ss : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize) (decClock s)).localsSize =
      sptLookup d (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize) (decClock s)).stackSize := rfl
  have e1 : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize) (decClock s)).stackSize =
      s.stackSize := rfl
  have e2 : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize) (decClock s)).stack =
      s.stack := rfl
  have e3 : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize) (decClock s)).stackMax =
      wordSemOptionMax s.stackMax (wordSemOptionAdd (wordSemStackSize s.stack) (sptLookup d s.stackSize)) :=
    rfl
  by_cases hdn : d ∈ ns
  · -- `Leaf` graph; the callee is one of the graphs in `max_depth_graphs`
    have hleaf : callGraph funs n ns (sptSize funs2) (.call none (some d) args none) = .leaf := by
      rw [callGraph, if_pos ⟨hdn, rfl⟩]
    rw [hleaf]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hdom d hdn)
    have hyc := subspt_lookup_some hcode hy
    rw [hcd] at hyc
    cases hyc
    have p := hIH funs d ns funs2 ⟨hsub, hcode, hcenv_ss, by rw [hr]; exact herr, hdn, hnd, hdom⟩
    rw [hr] at p
    dsimp only at p
    rw [e1, e2, e3] at p
    have hmem := mem_maxDepthGraphs s.stackSize ns funs funs2 ns d (a, prog) ⟨hdn, hy⟩
    simp only [maxDepthGraphs, hy] at hmem
    refine ⟨tail_mem_bound _ _ _ _ _ _ p.1 hmem, fun hne => ⟨?_, fun h => absurd h hloc_vac⟩⟩
    have hd' : maxDepth s.stackSize (callGraph funs d ns (sptSize funs2) prog) ≠ none := by
      intro h0
      apply optionLe_ne_none hmem hne.1
      rw [h0]
      cases sptLookup d s.stackSize <;> rfl
    exact (p.2 ⟨hne.1, hd'⟩).1
  · rcases hfl : sptLookup d funs with _ | ⟨a', body⟩
    · exact post_of_graph_none (by
        rw [callGraph_call_lookup_none (by simp [hdn]) hfl]; rfl)
    have hy := subspt_lookup_some hsub hfl
    have hyc := subspt_lookup_some hcode hy
    rw [hcd] at hyc
    cases hyc
    have hlen : ns.length < sptSize funs2 :=
      length_less_size d ns funs2 (a, prog) ⟨hdn, hdom, hnd, hy⟩
    rw [callGraph_call_tail hdn hfl, if_pos hlen, maxDepth_mkBranch]
    simp only [maxDepth]
    have hdom' : ∀ x, x ∈ d :: ns → (sptLookup x funs2).isSome = true := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hy]
      · exact hdom x hx
    have p := hIH funs d (d :: ns) funs2 ⟨hsub, hcode, hcenv_ss, by rw [hr]; exact herr,
      List.mem_cons_self, List.nodup_cons.mpr ⟨hdn, hnd⟩, hdom'⟩
    rw [hr] at p
    dsimp only at p
    rw [e1, e2, e3] at p
    simp only [maxDepthGraphs, hy] at p
    have hg2 := optionLe_maxDepthGraphs s.stackSize funs funs2 ns (d :: ns) ns
      ⟨fun x hx => List.mem_cons_of_mem _ hx, by simp⟩
    refine ⟨tail_fresh_bound _ _ _ _ _ _ _ p.1 hg2, fun hne => ⟨?_, fun h => absurd h hloc_vac⟩⟩
    have hld : sptLookup d s.stackSize ≠ none := by
      intro h0; apply hne.2; rw [h0]; rfl
    have hmd : maxDepth s.stackSize (callGraph funs d (d :: ns) (sptSize funs2) prog) ≠ none := by
      intro h0; apply hne.2; rw [h0, optionMap2_none_right]
    have hg2' := optionLe_ne_none hg2 hne.1
    refine (p.2 ⟨?_, hmd⟩).1
    intro h0
    rcases e1 : sptLookup d s.stackSize with _ | v1
    · exact hld e1
    rcases e2 : maxDepth s.stackSize (callGraph funs d (d :: ns) (sptSize funs2) prog) with _ | v2
    · exact hmd e2
    rcases e3 : maxDepthGraphs s.stackSize ns (d :: ns) funs funs2 with _ | v3
    · exact hg2' e3
    rw [e1, e2, e3] at h0
    simp [optionMap₂] at h0

end Flapjack.Compiler.Backend.WordDepthProof
