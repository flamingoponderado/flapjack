import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Seq

/-!
# `max_depth_call_graph_lemma`: `Loop` case

As in HOL (`evaluate_stack_swap`, `s_key_eq_stack_size`,
`evaluate_code_only_grows`): the entry cut only changes `locals`; a continuing
iteration composes the body and recursive-loop bounds as for `Seq`; an exiting
iteration keeps the body's bound.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact WordSemStackEq

namespace CallGraphLemmaLoopWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaLoopWitnesses

open CallGraphLemmaLoopWitnesses

/-- A run ending normally or by `Continue` keeps `stack_size` of the stack
(`evaluate_stack_swap` with `s_key_eq_stack_size`; Flapjack infrastructure). -/
theorem stackSize_of_cont {width : Nat} [NeZero width] {C F : Type}
    (c : WordLangProgHOL (BitVec width)) (v t : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width)) (h : evaluate c v = (r, t))
    (hr : r = none ∨ ∃ k, r = some (.continue k)) :
    wordSemStackSize t.stack = wordSemStackSize v.stack := by
  have hs := evaluateStackSwap c v
  unfold stackSwapPost at hs
  rw [h] at hs
  rcases hr with rfl | ⟨k, rfl⟩ <;> exact (sKeyEqStackSize _ _ hs.1).symm

/-- `max_depth_call_graph_lemma`, `Loop` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Loop {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width)) (exitNames : WordLangNumSetHOL)
    (s : WordSemStateFiniteExact width C F)
    (ih : (∀ v res s1, cutState (names, .ln) s = some v ∧ (res, s1) = evaluate c v ∧
        wordSemContLoop res = true ∧ s1.clock ≠ 0 →
        depthPost (wordSemSTOP (.loop names c exitNames)) (decClock s1)) ∧
      (∀ v, cutState (names, .ln) s = some v → depthPost c v)) :
    depthPost (.loop names c exitNames) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  simp only [callGraph]
  revert herr
  rw [evaluate]
  cases hcut : cutState (names, .ln) s with
  | none => intro h; exact absurd rfl h
  | some v =>
    dsimp only
    rw [fix_clock_evaluate]
    obtain ⟨l, hvl⟩ := cutStateConst _ _ _ hcut
    subst hvl
    cases hb : evaluate c { s with locals := l } with
    | mk r s1 =>
    dsimp only
    intro herr
    have herrb : (evaluate c { s with locals := l }).1 ≠ some .error := by
      rw [hb]; rintro rfl; exact herr (by simp [wordSemContLoop, wordSemExitLoop])
    have p1 := ih.2 _ hcut funs n ns funs2 ⟨hsub, hcode, hloc, herrb, hmem, hnd, hdom⟩
    rw [hb] at p1
    dsimp only at p1
    by_cases hG : maxDepthGraphs s.stackSize ns ns funs funs2 = none
    · refine ⟨?_, fun hne => absurd hG hne.1⟩
      rw [hG]; simp [optionMap₂, optionLe]
    by_cases hd : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) c) = none
    · refine ⟨?_, fun hne => absurd hd hne.2⟩
      rw [hd]; simp [optionMap₂, optionLe]
    obtain ⟨hss1, hls1⟩ := p1.2 ⟨hG, hd⟩
    by_cases hcont : wordSemContLoop r = true
    · have hr : r = none ∨ ∃ k, r = some (.continue k) := by
        rcases r with _ | ⟨_ | _ | _ | k | _ | _ | _ | _⟩ <;> simp_all [wordSemContLoop]
      simp only [hcont, if_true] at herr ⊢
      by_cases hz : s1.clock = 0
      · simp only [hz, ↓reduceDIte, flushState] at herr ⊢
        exact ⟨p1.1, fun _ => ⟨hss1, fun h => by simp at h⟩⟩
      · simp only [hz, ↓reduceDIte] at herr ⊢
        have hls1' : s1.localsSize = s.localsSize := by
          rcases hr with rfl | ⟨k, rfl⟩
          · exact hls1 (Or.inl rfl)
          · exact hls1 (Or.inr (Or.inr ⟨k, rfl⟩))
        have hstack := stackSize_of_cont c _ s1 r hb hr
        have hcode1 := evaluate_code_only_grows c _ r s1 hb
        have p2 := ih.1 _ r s1 ⟨hcut, hb.symm, hcont, hz⟩ funs n ns funs2
          ⟨hsub, sptSubsptTrans _ _ _ ⟨hcode, hcode1⟩,
            by show s1.localsSize = sptLookup n s1.stackSize; rw [hls1', hss1]; exact hloc,
            herr, hmem, hnd, hdom⟩
        simp only [wordSemSTOP, callGraph] at p2 herr ⊢
        have e1 : (decClock s1).stackSize = s.stackSize := hss1
        have e2 : (decClock s1).stack = s1.stack := rfl
        have e3 : (decClock s1).stackMax = s1.stackMax := rfl
        have e4 : (decClock s1).localsSize = s1.localsSize := rfl
        rw [e1, e2, e3, e4, hstack] at p2
        refine ⟨?_, fun hne => ?_⟩
        · have := seq_bound _ _ _ _ _ _ _ p1.1 p2.1
          rwa [optionMap2_max_idempot] at this
        · obtain ⟨hss2, hls2⟩ := p2.2 hne
          exact ⟨hss2, fun h => (hls2 h).trans hls1'⟩
    · simp only [hcont, if_false, Bool.false_eq_true] at herr ⊢
      by_cases hb0 : r = some (.break 0)
      · subst hb0
        simp only at herr ⊢
        cases hx : cutState (exitNames, .ln) s1 with
        | none => simp only [hx] at herr; exact absurd rfl herr
        | some s2 =>
            obtain ⟨l2, rfl⟩ := cutStateConst _ _ _ hx
            exact ⟨p1.1, fun _ => ⟨hss1, fun _ => hls1 (Or.inr (Or.inl ⟨0, rfl⟩))⟩⟩
      · split
        · exact absurd rfl hb0
        · refine ⟨p1.1, fun _ => ⟨hss1, fun h => hls1 ?_⟩⟩
          rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp_all [wordSemExitLoop]

end Flapjack.Compiler.Backend.WordDepthProof
