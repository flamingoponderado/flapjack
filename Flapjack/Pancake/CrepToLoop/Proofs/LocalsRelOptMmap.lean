import Flapjack.Pancake.CrepToLoop.StateRel

/-!
# crep_to_loop `OPT_MMAP` lookups under `locals_rel` over the exact carriers

Exact ports of the `[local]` theorems `opt_mmap_rhss_locals_rel` (2282),
`opt_mmap_lhss_locals_rel` (2300) and `not_mem_nlhss_lemma` (2322) of
`cakeml/pancake/proofs/crep_to_loopProofScript.sml` over the exact
`CrepSemHOLState` / `LoopSemStateFiniteExact` / `CrepToLoopContextExact`
carriers and `crepToLoopLocalsRelExact` (bead `flapjack-pxn.18.5.6.33.14`).
HOL `OPT_MMAP` is `List.mapM` in `Option` (as for the tagged `OPT_MMAP_APPEND`),
`EVERY P xs` is `∀ x ∈ xs, P x`, and `ALL_DISTINCT` is `List.Nodup`.
-/

namespace Flapjack

/-! The two owning carriers whose finite-map fields the statements traverse
(`ctxt.vars`, `s.locals`); same-module witnesses for the
`fmap_as_finite_support_relation` qualifier. -/
namespace CrepToLoopOptMmapFiniteMapWitnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Same-module re-export of the canonical `crep_to_loop$context` witness for
    the `fmap_as_finite_support := [vars]` qualifier on `not_mem_nlhss_lemma`. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopOptMmapFiniteMapWitnesses

/-- Exact HOL `not_mem_nlhss_lemma` (`crep_to_loopProofScript.sml:2322-2334`):
    `distinct_vars ctxt.vars ∧ ¬MEM vname lhss ∧ FLOOKUP ctxt.vars vname = SOME n ∧
      OPT_MMAP (FLOOKUP ctxt.vars) lhss = SOME nlhss ⇒ ¬MEM n nlhss`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_nlhss_lemma"
  (fmap_as_finite_support := [vars])]
theorem crepToLoop_not_mem_nlhss_lemma :
    ∀ (ctxt : CrepToLoopContextExact) (vname : Nat) (lhss : List Nat) (n : Nat)
      (nlhss : List Nat),
      crepToLoopDistinctVarsExact ctxt.vars ∧ vname ∉ lhss ∧
        ctxt.vars.lookup vname = some n ∧ lhss.mapM ctxt.vars.lookup = some nlhss →
      n ∉ nlhss := by
  intro ctxt vname lhss
  induction lhss with
  | nil => intro n nlhss ⟨_, _, _, h⟩; simp at h; subst h; simp
  | cons v vs ih =>
    intro n nlhss ⟨hd, hnm, hl, hm⟩
    simp only [List.mapM_cons] at hm
    cases hv : ctxt.vars.lookup v with
    | none => simp [hv] at hm
    | some m =>
      cases hvs : vs.mapM ctxt.vars.lookup with
      | none => simp [hv, hvs] at hm
      | some ms =>
        simp [hv, hvs] at hm
        subst hm
        simp only [List.mem_cons, not_or] at hnm ⊢
        refine ⟨fun hnmv => hnm.1 ?_, ih n ms ⟨hd, hnm.2, hl, hvs⟩⟩
        exact (crepToLoopDistinctVarsExact_iff_lookup ctxt.vars).mp hd
          vname v n m hl hv hnmv

/-- Exact HOL `opt_mmap_rhss_locals_rel` (`crep_to_loopProofScript.sml:2282-2298`):
    `OPT_MMAP (FLOOKUP s.locals) rhss = SOME ws ∧ locals_rel ctxt l s.locals t.locals ⇒
      ∃nrhss. OPT_MMAP (FLOOKUP ctxt.vars) rhss = SOME nrhss ∧
        LENGTH nrhss = LENGTH rhss ∧ EVERY (λn. n ∈ domain l) nrhss ∧
        get_vars nrhss t = SOME (MAP wlab_wloc ws)`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "opt_mmap_rhss_locals_rel"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars, CrepSemHOLState.locals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_opt_mmap_rhss_locals_rel {width : Nat} [NeZero width] {σ F : Type} :
    ∀ (rhss : List Nat) (ws : List (HolWordLab width)) (s : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (l : NumSet),
      rhss.mapM s.locals.lookup = some ws ∧ crepToLoopLocalsRelExact ctxt l s.locals t.locals →
      ∃ nrhss, rhss.mapM ctxt.vars.lookup = some nrhss ∧ nrhss.length = rhss.length ∧
        (∀ n ∈ nrhss, sptMem n l) ∧ LoopSemStateFiniteExact.getVars nrhss t = some (ws.map wlabWlocHOL) := by
  intro rhss
  induction rhss with
  | nil => intro ws s t ctxt l ⟨h, _⟩; simp at h; subst h; exact ⟨[], by simp⟩
  | cons v vs ih =>
    intro ws s t ctxt l ⟨hm, hr⟩
    simp only [List.mapM_cons] at hm
    cases hv : s.locals.lookup v with
    | none => simp [hv] at hm
    | some w =>
      cases hvs : vs.mapM s.locals.lookup with
      | none => simp [hv, hvs] at hm
      | some ws' =>
        simp [hv, hvs] at hm
        subst hm
        obtain ⟨n, hn1, hn2, hn3⟩ := hr.2.2.2 v w hv
        obtain ⟨ns, h1, h2, h3, h4⟩ := ih ws' s t ctxt l ⟨hvs, hr⟩
        refine ⟨n :: ns, by simp [List.mapM_cons, hn1, h1], by simp [h2], ?_, ?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hn2
          · exact h3 k hk
        · simp [LoopSemStateFiniteExact.getVars, hn3, h4]

/-- Exact HOL `opt_mmap_lhss_locals_rel` (`crep_to_loopProofScript.sml:2300-2320`):
    `EVERY (λv. IS_SOME (FLOOKUP s.locals v)) lhss ∧ ALL_DISTINCT lhss ∧
      locals_rel ctxt l s.locals t.locals ⇒
      ∃nlhss. OPT_MMAP (FLOOKUP ctxt.vars) lhss = SOME nlhss ∧
        LENGTH nlhss = LENGTH lhss ∧ EVERY (λn. n ∈ domain l) nlhss ∧
        ALL_DISTINCT nlhss`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "opt_mmap_lhss_locals_rel"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars, CrepSemHOLState.locals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_opt_mmap_lhss_locals_rel {width : Nat} [NeZero width] {σ F : Type} :
    ∀ (lhss : List Nat) (s : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (l : NumSet),
      (∀ v ∈ lhss, (s.locals.lookup v).isSome) ∧ lhss.Nodup ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals →
      ∃ nlhss, lhss.mapM ctxt.vars.lookup = some nlhss ∧ nlhss.length = lhss.length ∧
        (∀ n ∈ nlhss, sptMem n l) ∧ nlhss.Nodup := by
  intro lhss
  induction lhss with
  | nil => intro s t ctxt l _; exact ⟨[], by simp⟩
  | cons v vs ih =>
    intro s t ctxt l ⟨hs, hnd, hr⟩
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hs v List.mem_cons_self)
    obtain ⟨n, hn1, hn2, _⟩ := hr.2.2.2 v w hw
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨ns, h1, h2, h3, h4⟩ :=
      ih s t ctxt l ⟨fun x hx => hs x (List.mem_cons_of_mem _ hx), hnd'.2, hr⟩
    refine ⟨n :: ns, by simp [List.mapM_cons, hn1, h1], by simp [h2], ?_, ?_⟩
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hn2
      · exact h3 k hk
    · exact List.nodup_cons.mpr
        ⟨crepToLoop_not_mem_nlhss_lemma ctxt v vs n ns ⟨hr.1, hnd'.1, hn1, h1⟩, h4⟩

end Flapjack
