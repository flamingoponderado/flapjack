import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.LoopRecursion

/-!
# `evaluate_remove_dead` Loop helper

`word_allocProofScript.sml:3728-3898` `evaluate_remove_dead_Loop_helper`: the Loop
case of `evaluate_remove_dead`, by induction on the clock, from the body
statement for the loop's own context.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

/-- The loop clause of `remove_dead` (Flapjack infrastructure). -/
theorem removeDead_loop {width : Nat} [NeZero width] (names exitNames : NumSet)
    (body : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet)) :
    removeDead (.loop names body exitNames) live nlive lt =
      (.loop names (removeDead body names [] ((names, exitNames) :: lt)).1 exitNames, names, []) := by
  rw [removeDead]

/-- An identity-coloured cut moves to a target whose locals agree on the cut names
(Flapjack infrastructure from HOL `strong_locals_rel_I_cut_env`). -/
theorem cutStateRemoveDead {width : Nat} [NeZero width] {C F : Type}
    (names : NumSet) (st entry : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (hl : strongLocalsRel id (sptDomain names) st.locals t)
    (hcut : cutState (names, .ln) st = some entry) :
    cutState (names, .ln) { st with locals := t, store := tstore } =
      some { entry with store := tstore } := by
  unfold cutState at hcut ⊢
  cases henv : wordSemCutEnv (names, .ln) st.locals with
  | none => rw [henv] at hcut; cases hcut
  | some env =>
    rw [henv] at hcut
    cases hcut
    have h := strongLocalsRelICutEnv (names, .ln) st t env
      ⟨fun k v hk => hl k v ⟨by simpa [sptDomain, sptLookup] using hk.1, hk.2⟩, henv⟩
    simp only [h]

namespace EvaluateRemoveDeadLoopWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadLoopWitnesses

set_option maxRecDepth 4000 in
/-- Exact HOL `evaluate_remove_dead_Loop_helper` (`word_allocProofScript.sml:3728-3898`):
the HOL premises at `Loop names body exit_names`, including `nlivein = []`, and the
universally quantified body statement for the loop's own context
(`live = names`, `nlive = []`, `(names, exit_names) :: lt`), give HOL's conclusion.
`removeDeadPost` spells HOL's result case expression. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead_Loop_helper"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDeadLoopHelper {width : Nat} [NeZero width] {C F : Type} :
    ∀ (st : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
      (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width)) (names : NumSet)
      (body : WordLangProgHOL (BitVec width)) (exitNames live : NumSet)
      (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
      (prog' : WordLangProgHOL (BitVec width)) (livein : NumSet) (nlivein : List WordStoreHOL)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
      strongLocalsRel id (sptDomain livein) st.locals t ∧
        liveStoreRel nlivein st.store tstore ∧
        evaluate (.loop names body exitNames) st = (res, rst) ∧
        flatExpConventions body = true ∧
        removeDead (.loop names body exitNames) live nlive lt = (prog', livein, nlivein) ∧
        nlivein = [] ∧ res ≠ some .error ∧
        (∀ (st' : WordSemStateFiniteExact width C F) (t' : Spt (WordLocW width))
            (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width))
            (prog'' : WordLangProgHOL (BitVec width)) (livein' : NumSet)
            (nlivein' : List WordStoreHOL) (res' : Option (WordSemResult width))
            (rst' : WordSemStateFiniteExact width C F),
          strongLocalsRel id (sptDomain livein') st'.locals t' ∧
            liveStoreRel nlivein' st'.store tstore' ∧
            evaluate body st' = (res', rst') ∧
            removeDead body names [] ((names, exitNames) :: lt) = (prog'', livein', nlivein') ∧
            res' ≠ some .error →
          ∃ (t'' : Spt (WordLocW width)) (tstore'' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
            evaluate prog'' { st' with locals := t', store := tstore' } =
              (res', { rst' with locals := t'', store := tstore'' }) ∧
            removeDeadPost names [] ((names, exitNames) :: lt) res' rst' t'' tstore'') →
      ∃ (t' : Spt (WordLocW width)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
        evaluate prog' { st with locals := t, store := tstore } =
          (res, { rst with locals := t', store := tstore' }) ∧
        removeDeadPost live nlive lt res rst t' tstore' := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  suffices H : ∀ n (st : WordSemStateFiniteExact width C F), st.clock = n →
      ∀ (t : Spt (WordLocW width)) (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width))
        (names : NumSet) (body : WordLangProgHOL (BitVec width)) (exitNames live : NumSet)
        (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
        (prog' : WordLangProgHOL (BitVec width)) (livein : NumSet) (nlivein : List WordStoreHOL)
        (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
        strongLocalsRel id (sptDomain livein) st.locals t ∧
          liveStoreRel nlivein st.store tstore ∧
          evaluate (.loop names body exitNames) st = (res, rst) ∧
          flatExpConventions body = true ∧
          removeDead (.loop names body exitNames) live nlive lt = (prog', livein, nlivein) ∧
          nlivein = [] ∧ res ≠ some .error ∧
          (∀ (st' : WordSemStateFiniteExact width C F) (t' : Spt (WordLocW width))
              (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width))
              (prog'' : WordLangProgHOL (BitVec width)) (livein' : NumSet)
              (nlivein' : List WordStoreHOL) (res' : Option (WordSemResult width))
              (rst' : WordSemStateFiniteExact width C F),
            strongLocalsRel id (sptDomain livein') st'.locals t' ∧
              liveStoreRel nlivein' st'.store tstore' ∧
              evaluate body st' = (res', rst') ∧
              removeDead body names [] ((names, exitNames) :: lt) = (prog'', livein', nlivein') ∧
              res' ≠ some .error →
            ∃ (t'' : Spt (WordLocW width)) (tstore'' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
              evaluate prog'' { st' with locals := t', store := tstore' } =
                (res', { rst' with locals := t'', store := tstore'' }) ∧
              removeDeadPost names [] ((names, exitNames) :: lt) res' rst' t'' tstore'') →
        ∃ (t' : Spt (WordLocW width)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
          evaluate prog' { st with locals := t, store := tstore } =
            (res, { rst with locals := t', store := tstore' }) ∧
          removeDeadPost live nlive lt res rst t' tstore' by
    intro st; exact H st.clock st rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  rintro st hn t tstore names body exitNames live nlive lt prog' livein nlivein res rst
    ⟨hl, hs, hev, hflat, hrd, hnl, herr, ihb⟩
  rw [removeDead_loop] at hrd
  rcases hrdb : removeDead body names [] ((names, exitNames) :: lt) with ⟨body', liveb, nliveb⟩
  rw [hrdb] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hstore : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hstore
  rw [ht] at hev
  cases hcut : cutState (names, .ln) st with
  | none =>
    rw [hcut] at hev
    simp only [Prod.mk.injEq] at hev
    exact absurd hev.1.symm herr
  | some entry =>
    rw [hcut] at hev
    dsimp only at hev
    have hcutT := cutStateRemoveDead names st entry t st.store hl hcut
    have hentryStore : entry.store = st.store := by
      unfold cutState at hcut
      cases henv : wordSemCutEnv (names, .ln) st.locals with
      | none => rw [henv] at hcut; cases hcut
      | some env => rw [henv] at hcut; cases hcut; rfl
    have hentryT : { entry with store := st.store } = entry := by rw [← hentryStore]
    rw [hentryT] at hcutT
    rcases hb : evaluate body entry with ⟨res', s1⟩
    rw [hb] at hev
    dsimp only at hev
    have herr' : res' ≠ some .error := by
      rintro rfl
      simp only [wordSemContLoop, Bool.false_eq_true, if_false, wordSemExitLoop,
        Prod.mk.injEq] at hev
      exact herr hev.1.symm
    obtain ⟨t'', tstore'', hbT, hpost⟩ :=
      ihb entry entry.locals entry.store body' liveb nliveb res' s1
        ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hb, hrdb, herr'⟩
    have hentry2 : { entry with locals := entry.locals, store := entry.store } = entry := rfl
    rw [hentry2] at hbT
    have hstate : ∀ (a : Spt (WordLocW width)) (b : HolFiniteMapExact WordStoreHOL (WordLocW width)),
        decClock { s1 with locals := a, store := b } = { decClock s1 with locals := a, store := b } :=
      fun _ _ => rfl
    -- the recursive iteration shared by `NONE` and `Continue 0`
    have recur : strongLocalsRel id (sptDomain names) s1.locals t'' → s1.clock ≠ 0 →
        evaluate (wordSemSTOP (.loop names body exitNames)) (decClock s1) = (res, rst) →
        ∃ (t' : Spt (WordLocW width)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
          evaluate (wordSemSTOP (.loop names body' exitNames))
              (decClock { s1 with locals := t'', store := s1.store }) =
            (res, { rst with locals := t', store := tstore' }) ∧
          removeDeadPost live nlive lt res rst t' tstore' := by
      intro hl1 hz hrec
      have hlt : (decClock s1).clock < n := by
        have := loopBodyRecursiveClockLt (names, .ln) body st entry s1 res' hcut hb hz
        omega
      rw [hstate]
      exact ih _ hlt (decClock s1) rfl t'' s1.store names body exitNames live nlive lt
        (.loop names body' exitNames) names [] res rst
        ⟨hl1, liveStoreRelRefl _ _, hrec, hflat, by rw [removeDead_loop, hrdb], rfl, herr, ihb⟩
    rw [ht, hcutT]
    dsimp only
    rw [hbT]
    dsimp only
    cases res' with
    | none =>
      obtain ⟨hl1, hs1⟩ := hpost
      have hst : s1.store = tstore'' := (liveStoreRelNil _ _).mp hs1
      subst hst
      simp only [wordSemContLoop, if_true] at hev ⊢
      by_cases hz : s1.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at hev ⊢
        obtain ⟨rfl, rfl⟩ := hev
        exact ⟨(flushState true s1).locals, (flushState true s1).store,
          ⟨rfl, by simp [flushState, hz]⟩, rfl, rfl⟩
      · simp only [hz, if_false] at hev ⊢
        exact recur hl1 hz hev
    | some r =>
      cases r with
      | error => exact absurd rfl herr'
      | «continue» k =>
        obtain ⟨hst, hl1⟩ := hpost
        subst hst
        cases k with
        | zero =>
          simp only [sptOel] at hl1
          simp only [wordSemContLoop, decide_true, if_true] at hev ⊢
          by_cases hz : s1.clock = 0
          · simp only [hz, if_true, Prod.mk.injEq] at hev ⊢
            obtain ⟨rfl, rfl⟩ := hev
            exact ⟨(flushState true s1).locals, (flushState true s1).store,
              ⟨rfl, by simp [flushState, hz]⟩, rfl, rfl⟩
          · simp only [hz, if_false] at hev ⊢
            exact recur hl1 hz hev
        | succ k =>
          simp only [wordSemContLoop, Nat.add_one_ne_zero, decide_false, Bool.false_eq_true,
            if_false, wordSemExitLoop, Nat.add_sub_cancel, Prod.mk.injEq] at hev ⊢
          obtain ⟨rfl, rfl⟩ := hev
          refine ⟨t'', s1.store, ⟨rfl, rfl⟩, rfl, ?_⟩
          simpa [sptOel] using hl1
      | «break» k =>
        obtain ⟨hst, hl1⟩ := hpost
        subst hst
        cases k with
        | zero =>
          simp only [sptOel] at hl1
          simp only [wordSemContLoop, Bool.false_eq_true, if_false] at hev ⊢
          cases hexit : cutState (exitNames, .ln) s1 with
          | none =>
            rw [hexit] at hev
            simp only [Prod.mk.injEq] at hev
            exact absurd hev.1.symm herr
          | some s2 =>
            rw [hexit] at hev
            simp only [Prod.mk.injEq] at hev
            obtain ⟨rfl, rfl⟩ := hev
            have hcutE := cutStateRemoveDead exitNames s1 s2 t'' s1.store hl1 hexit
            have hs2 : s2.store = s1.store := by
              unfold cutState at hexit
              cases henv : wordSemCutEnv (exitNames, .ln) s1.locals with
              | none => rw [henv] at hexit; cases hexit
              | some env => rw [henv] at hexit; cases hexit; rfl
            have hs2' : { s2 with store := s1.store } = s2 := by rw [← hs2]
            rw [hs2'] at hcutE
            rw [hcutE]
            exact ⟨s2.locals, s2.store, rfl, strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _⟩
        | succ k =>
          simp only [wordSemContLoop, Bool.false_eq_true, if_false, wordSemExitLoop,
            Nat.add_sub_cancel, Prod.mk.injEq] at hev ⊢
          obtain ⟨rfl, rfl⟩ := hev
          refine ⟨t'', s1.store, ⟨rfl, rfl⟩, rfl, ?_⟩
          simpa [sptOel] using hl1
      | result a b | exception a b | timeOut | notEnoughSpace | finalFfi e =>
        obtain ⟨hlo, hst⟩ := hpost
        subst hlo hst
        simp only [wordSemContLoop, Bool.false_eq_true, if_false, wordSemExitLoop,
          Prod.mk.injEq] at hev ⊢
        obtain ⟨rfl, rfl⟩ := hev
        exact ⟨s1.locals, s1.store, ⟨rfl, rfl⟩, rfl, rfl⟩


end Flapjack.WordAlloc
