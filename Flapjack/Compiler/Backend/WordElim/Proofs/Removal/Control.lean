module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.Basic

@[expose] public section

/-!
# `word_removal_lemma`: the control cases

The `MustTerminate`, `Seq`, `If` and `Loop` cases of HOL `word_removal_lemma`
(`word_elimProofScript.sml:1054-1093`, `1543-1599`).  Each piece is HOL's
statement (`WordRemovalGoal`) for that constructor, given exactly the induction
hypotheses of the rebound `evaluate_ind` clause instantiated at that statement.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps

namespace WordElimRemovalControlSupport
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordElimRemovalControlSupport

section ControlHelpers
variable {width : Nat} [NeZero width] {C F : Type}

theorem cutState_withCode (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F)
    (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    cutState names { s with code := c } = (cutState names s).map fun x => { x with code := c } := by
  unfold cutState
  dsimp only
  split <;> rfl

theorem cutState_locsWithin (names : WordLangCutsetsHOL) (s v : WordSemStateFiniteExact width C F)
    (h : cutState names s = some v) : LocsWithin v s := by
  unfold cutState at h
  split at h
  · cases h
  · rename_i env henv
    cases h
    intro n hn
    rw [sptMem_findLocState] at hn ⊢
    rcases hn with h | h
    · exact Or.inl (locsWithin_cutEnv_locals s names henv n h)
    · exact Or.inr h

theorem noInstall_mustTerminate {p : WordLangProgHOL (BitVec width)}
    (h : noInstallSubprogsHOL (.mustTerminate p) = true) : noInstallSubprogsHOL p = true := by
  simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using h

theorem noInstall_seq {p q : WordLangProgHOL (BitVec width)}
    (h : noInstallSubprogsHOL (.seq p q) = true) :
    noInstallSubprogsHOL p = true ∧ noInstallSubprogsHOL q = true := by
  simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using h

theorem noInstall_ite {cmp : Cmp} {r : Nat} {ri : WordRegImm (BitVec width)}
    {p q : WordLangProgHOL (BitVec width)}
    (h : noInstallSubprogsHOL (.ite cmp r ri p q) = true) :
    noInstallSubprogsHOL p = true ∧ noInstallSubprogsHOL q = true := by
  simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using h

theorem noInstall_loop {names exitNames : WordLangNumSetHOL} {p : WordLangProgHOL (BitVec width)}
    (h : noInstallSubprogsHOL (.loop names p exitNames) = true) :
    noInstallSubprogsHOL p = true := by
  simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using h

theorem sptDomainSet_union_left {α β : Type} {a b : Spt α} {r : Spt β}
    (h : sptDomainSet (sptUnion a b) ⊆ sptDomainSet r) : sptDomainSet a ⊆ sptDomainSet r :=
  fun n hn => h ((sptMem_sptUnion a b n).mpr (Or.inl hn))

theorem sptDomainSet_union_right {α β : Type} {a b : Spt α} {r : Spt β}
    (h : sptDomainSet (sptUnion a b) ⊆ sptDomainSet r) : sptDomainSet b ⊆ sptDomainSet r :=
  fun n hn => h ((sptMem_sptUnion a b n).mpr (Or.inr hn))

/-- The code of a no-install run is unchanged. -/
theorem code_of_evaluate {p : WordLangProgHOL (BitVec width)} {s s1 : WordSemStateFiniteExact width C F}
    {res : Option (WordSemResult width)} (hev : evaluate p s = (res, s1))
    (hni : noInstallSubprogsHOL p = true) (hc : noInstallCode s.code) : s1.code = s.code := by
  have := code_evaluate p s hni hc
  rw [hev] at this
  exact this

theorem gcFun_of_evaluate {p : WordLangProgHOL (BitVec width)} {s s1 : WordSemStateFiniteExact width C F}
    {res : Option (WordSemResult width)} (hev : evaluate p s = (res, s1)) : s1.gcFun = s.gcFun :=
  (evaluate_consts p s res s1 hev).1.symm

end ControlHelpers

section ControlCases
variable {width : Nat} [NeZero width] {C F : Type}

theorem wordStateRel_clock_termdep {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) (a b : Nat) :
    wordStateRel reachable { s with clock := a, termdep := b } { t with clock := a, termdep := b } := by
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  exact wordStateRel_withCode_within h rfl fun _ h => h

theorem wordStateRel_decClock {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) : wordStateRel reachable (decClock s) (decClock t) := by
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  exact wordStateRel_withCode_within h rfl fun _ h => h

theorem wordStateRel_flushState {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) (b : Bool) :
    wordStateRel reachable (flushState b s) (flushState b t) := by
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  have : flushState b { s with code := c } = { flushState b s with code := c } := by
    cases b <;> rfl
  rw [this]
  exact wordStateRel_withCode_within h (by cases b <;> rfl) (locsWithin_flushState s b)

theorem wordStateRel_clock {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) : t.clock = s.clock :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wordStateRel_termdep {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) : t.termdep = s.termdep :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Case `MustTerminate` of HOL `word_removal_lemma`
    (`Resume word_removal_lemma[MustTerminate]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_MustTerminate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      (s.termdep ≠ 0 →
        WordRemovalGoal p
          { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }) →
      WordRemovalGoal (.mustTerminate p) s := by
  intro p s ih result new_state reachable t ⟨hev, herr, hrel, hg, hni, hnic, hnict, hfwr, hcc⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at hev
  rw [ht]
  have htd := wordStateRel_termdep hrel
  have htc := wordStateRel_clock hrel
  rw [htd]
  by_cases hz : s.termdep = 0
  · simp only [hz, if_true] at hev
    cases hev
    exact absurd rfl herr
  simp only [hz, if_false] at hev ⊢
  rcases h1 : evaluate p
      { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } with ⟨r1, s1⟩
  rw [h1] at hev
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp only at hev
    cases hev
    exact herr rfl
  obtain ⟨t1, ht1, hrel1, hloc1⟩ := ih hz r1 s1 reachable
    { t with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }
    ⟨h1, hr1, wordStateRel_clock_termdep hrel _ _, hg, noInstall_mustTerminate hni, hnic, hnict,
      hfwr, hcc⟩
  rw [ht1]
  rcases r1 with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp only at hev ⊢ <;> cases hev <;>
    first
      | exact absurd rfl herr
      | exact ⟨_, rfl, by rw [htc]; exact wordStateRel_clock_termdep hrel1 _ _, hloc1⟩

/-- Case `Seq` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Seq]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Seq :
    ∀ (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      (∀ res s1, (res, s1) = evaluate c1 s ∧ res = none → WordRemovalGoal c2 s1) ∧
        WordRemovalGoal c1 s →
      WordRemovalGoal (.seq c1 c2) s := by
  intro c1 c2 s ⟨ih2, ih1⟩ result new_state reachable t
    ⟨hev, herr, hrel, hg, hni, hnic, hnict, hfwr, hcc⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at hev
  rw [ht]
  obtain ⟨hni1, hni2⟩ := noInstall_seq hni
  rcases h1 : evaluate c1 s with ⟨r1, s1⟩
  rw [h1] at hev
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    cases hev
    exact herr rfl
  obtain ⟨t1, ht1, hrel1, hloc1⟩ := ih1 r1 s1 reachable t
    ⟨h1, hr1, hrel, hg, hni1, hnic, hnict, sptDomainSet_union_left hfwr, hcc⟩
  rw [ht1]
  cases r1 with
  | some x =>
    cases hev
    exact ⟨t1, rfl, hrel1, hloc1⟩
  | none =>
    simp only at hev ⊢
    have hcode1 := code_of_evaluate h1 hni1 hnic
    have hcodet := code_of_evaluate ht1 hni1 hnict
    exact ih2 none s1 ⟨h1.symm, rfl⟩ result new_state reachable t1
      ⟨hev, herr, hrel1, (gcFun_of_evaluate h1) ▸ hg, hni2, hcode1 ▸ hnic, hcodet ▸ hnict,
        sptDomainSet_union_right hfwr, hcode1 ▸ hcc⟩

/-- Case `If` of HOL `word_removal_lemma` (`Resume word_removal_lemma[If]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_If :
    ∀ (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width)) (c1 c2 : WordLangProgHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F),
      (∀ v3 v4 x y v, (getVar r1 s, WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ v = true → WordRemovalGoal c1 s) ∧
      (∀ v3 v4 x y v, (getVar r1 s, WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ ¬ v = true → WordRemovalGoal c2 s) →
      WordRemovalGoal (.ite cmp r1 ri c1 c2) s := by
  intro cmp r1 ri c1 c2 s ⟨ih1, ih2⟩ result new_state reachable t
    ⟨hev, herr, hrel, hg, hni, hnic, hnict, hfwr, hcc⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at hev
  rw [ht]
  obtain ⟨hni1, hni2⟩ := noInstall_ite hni
  have hv : getVar r1 t = getVar r1 s := word_state_rel_get_var hrel
  have hvi : WordSemStateFiniteExact.getVarImm ri t = WordSemStateFiniteExact.getVarImm ri s := by
    cases ri with
    | reg n => exact word_state_rel_get_var hrel
    | imm w => rfl
  rw [hv, hvi]
  rcases hx : getVar r1 s with _ | x <;> rcases hy : WordSemStateFiniteExact.getVarImm ri s with _ | y <;>
    simp only [hx, hy] at hev ⊢
  all_goals try (cases hev; exact absurd rfl herr)
  rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hc] at hev ⊢
  · cases hev; exact absurd rfl herr
  · exact ih2 _ _ x y false ⟨rfl, hx, hy, hc, by simp⟩ result new_state reachable t
      ⟨hev, herr, hrel, hg, hni2, hnic, hnict, sptDomainSet_union_right hfwr, hcc⟩
  · exact ih1 _ _ x y true ⟨rfl, hx, hy, hc, rfl⟩ result new_state reachable t
      ⟨hev, herr, hrel, hg, hni1, hnic, hnict, sptDomainSet_union_left hfwr, hcc⟩

end ControlCases

section LoopCase
variable {width : Nat} [NeZero width] {C F : Type}

theorem destResultLoc_exitLoop (r : Option (WordSemResult width)) (n : Nat)
    (h : destResultLoc (wordSemExitLoop r) n) : destResultLoc r n := by
  rcases r with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> exact h

theorem cutState_code {names : WordLangCutsetsHOL} {s v : WordSemStateFiniteExact width C F}
    (h : cutState names s = some v) : v.code = s.code ∧ v.gcFun = s.gcFun := by
  obtain ⟨l, rfl⟩ := cutStateConst _ _ _ h
  exact ⟨rfl, rfl⟩

/-- Case `Loop` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Loop]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Loop :
    ∀ (names : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width))
      (exitNames : WordLangNumSetHOL) (s : WordSemStateFiniteExact width C F),
      (∀ v res s1, cutState (names, .ln) s = some v ∧ (res, s1) = evaluate c v ∧
          wordSemContLoop res = true ∧ s1.clock ≠ 0 →
        WordRemovalGoal (wordSemSTOP (.loop names c exitNames)) (decClock s1)) ∧
      (∀ v, cutState (names, .ln) s = some v → WordRemovalGoal c v) →
      WordRemovalGoal (.loop names c exitNames) s := by
  intro names c exitNames s ⟨ihStep, ihBody⟩ result new_state reachable t
    ⟨hev, herr, hrel, hg, hni, hnic, hnict, hfwr, hcc⟩
  obtain ⟨code, hc⟩ := wordStateRel_exists_withCode hrel
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at hev
  rw [ht]
  have hnib := noInstall_loop hni
  rcases hcs : cutState (names, .ln) s with _ | v
  · simp only [hcs] at hev
    cases hev
    exact absurd rfl herr
  simp only [hcs] at hev
  have hct : cutState (names, .ln) t = some { v with code := code } := by
    rw [hc, cutState_withCode, hcs]; rfl
  rw [hct]
  simp only
  obtain ⟨hvcode, hvgc⟩ := cutState_code hcs
  have hrelv : wordStateRel reachable v { v with code := code } := by
    subst hc
    exact wordStateRel_withCode_within hrel hvcode (cutState_locsWithin _ _ _ hcs)
  have htcode : t.code = code := by rw [hc]
  rcases h1 : evaluate c v with ⟨r1, s1⟩
  rw [h1] at hev
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp [wordSemContLoop, wordSemExitLoop] at hev
    exact herr hev.1.symm
  obtain ⟨t1, ht1, hrel1, hloc1⟩ := ihBody v hcs r1 s1 reachable { v with code := code }
    ⟨h1, hr1, hrelv, hvgc ▸ hg, hnib, hvcode ▸ hnic, htcode ▸ hnict, hfwr, hvcode ▸ hcc⟩
  rw [ht1]
  simp only
  have hs1code : s1.code = s.code := (code_of_evaluate h1 hnib (hvcode ▸ hnic)).trans hvcode
  have ht1code : t1.code = code := code_of_evaluate ht1 hnib (htcode ▸ hnict)
  have hs1gc : s1.gcFun = s.gcFun := (gcFun_of_evaluate h1).trans hvgc
  rw [wordStateRel_clock hrel1]
  by_cases hcl : wordSemContLoop r1 = true
  · simp only [hcl, if_true] at hev ⊢
    by_cases hz : s1.clock = 0
    · simp only [hz, if_true] at hev ⊢
      cases hev
      exact ⟨_, rfl, wordStateRel_flushState hrel1 true, fun n hn => hn.elim⟩
    · simp only [hz, if_false] at hev ⊢
      exact ihStep v r1 s1 ⟨hcs, h1.symm, hcl, hz⟩ result new_state reachable (decClock t1)
        ⟨hev, herr, wordStateRel_decClock hrel1, hs1gc ▸ hg, hni, hs1code ▸ hnic,
          (show (decClock t1).code = t.code from ht1code.trans htcode.symm) ▸ hnict,
          hfwr, hs1code ▸ hcc⟩
  · simp only [hcl, Bool.false_eq_true, if_false] at hev ⊢
    split at hev
    · rename_i hb
      split at hev
      · cases hev; exact absurd rfl herr
      · rename_i s2 hce
        obtain ⟨hr, hn⟩ := Prod.mk.inj hev
        subst hr hn
        obtain ⟨c1, hc1⟩ := wordStateRel_exists_withCode hrel1
        have hce' : cutState (exitNames, .ln) t1 = some { s2 with code := c1 } := by
          rw [hc1, cutState_withCode, hce]; rfl
        simp only [hce']
        refine ⟨_, rfl, ?_, fun n hn => hn.elim⟩
        have hrel1' := hrel1
        rw [hc1] at hrel1'
        exact wordStateRel_withCode_within hrel1' (cutState_code hce).1
          (cutState_locsWithin _ _ _ hce)
    · cases hev
      exact ⟨t1, rfl, hrel1, fun n hn => hloc1 (destResultLoc_exitLoop r1 n hn)⟩

end LoopCase

end Flapjack.Compiler.Backend.WordElim
