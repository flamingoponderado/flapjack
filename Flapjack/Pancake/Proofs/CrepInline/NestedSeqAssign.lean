import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Semantics.CrepProps

/-!
# crep_inline: `OPT_MMAP` locals helpers and `evaluate_nested_seq_assign`

Counterparts of `cakeml/pancake/proofs/crep_inlineProofScript.sml:1802-1891`
(bead `flapjack-pxn.18.5.5.47.1`), used by `transform_eoc_correct` and
`transform_branch_correct`.  `fdoms_eq_opt_mmap_flookup_some` (`:1833`) is
already ported in `Flapjack.Pancake.Proofs.CrepInline`.

Renderings, as in the other crep_inline ports:
* `FLOOKUP fm` is `fm.lookup`, `OPT_MMAP` is `List.mapM`;
* `fm |+ nv` is `HolFiniteMapExact.updateEq`, `fm |++ l` is `updateListEq`,
  `fm \\ x` is `eraseEq`;
* `eval s` is the tagged `evalCrepSemHOLExp s`, `var_cexp` is `crepExpVarsHOL`,
  `MAP2` is `panMap2`, `nested_seq` is `crepNestedSeqHOL`, `evaluate` is
  `evalCrepSemHOLProgExact`, `ALL_DISTINCT` is `List.Nodup`, and `state_rel` is
  the tagged `CrepInlineExact.crepInlineStateRelExact`.
-/

namespace Flapjack

namespace CrepInlineNestedSeqAssign

open HolFiniteMapExact
open CrepInlineExact

/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Local support: a total `mapM` is total on any pointwise-defined map. -/
private theorem mapM_some_of_pointwise {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (h : ∀ x, (∃ y, f x = some y) → ∃ z, g x = some z) :
    ∀ (vs : List α) (vals : List β), vs.mapM f = some vals → ∃ z, vs.mapM g = some z
  | [], _, _ => ⟨[], rfl⟩
  | v :: vs, vals, hv => by
      simp only [List.mapM_cons] at hv
      cases hf : f v with
      | none => simp [hf] at hv
      | some y =>
          cases hr : vs.mapM f with
          | none => simp [hf, hr] at hv
          | some ys =>
              obtain ⟨z, hz⟩ := h v ⟨y, hf⟩
              obtain ⟨zs, hzs⟩ := mapM_some_of_pointwise f g h vs ys hr
              exact ⟨z :: zs, by simp [List.mapM_cons, hz, hzs]⟩

/-- Exact HOL `opt_mmap_some_imp_fupdate_exist_some`
    (`crep_inlineProofScript.sml:1802-1812`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_some_imp_fupdate_exist_some"
  (fmap_as_finite_support_relation := [fm])]
theorem optMmapSomeImpFupdateExistSome {α β : Type} [DecidableEq α] :
    ∀ (vs : List α) (fm : HolFiniteMapExact α β) (vals : List β) (nv : α × β),
      vs.mapM fm.lookup = some vals → ∃ z, vs.mapM (fm.updateEq nv).lookup = some z := by
  intro vs fm vals nv h
  refine mapM_some_of_pointwise _ _ (fun x ⟨y, hy⟩ => ?_) vs vals h
  rw [lookup_updateEq]
  by_cases hx : x = nv.1
  · exact ⟨nv.2, by simp [FUPDATE_HOL, hx]⟩
  · exact ⟨y, by simp [FUPDATE_HOL, hx, hy]⟩

/-- Exact HOL `opt_mmap_some_imp_fupdate_list_exist_some`
    (`crep_inlineProofScript.sml:1814-1823`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml"
  "opt_mmap_some_imp_fupdate_list_exist_some"
  (fmap_as_finite_support_relation := [fm])]
theorem optMmapSomeImpFupdateListExistSome {α β : Type} [DecidableEq α] :
    ∀ (xs : List α) (ys : List β) (vs : List α) (fm : HolFiniteMapExact α β) (vals : List β),
      vs.mapM fm.lookup = some vals ∧ xs.length = ys.length →
        ∃ z, vs.mapM (fm.updateListEq (xs.zip ys)).lookup = some z := by
  intro xs
  induction xs with
  | nil =>
      intro ys vs fm vals ⟨h, _⟩
      exact ⟨vals, by simpa [updateListEq, FUPDATE_LIST_HOL] using h⟩
  | cons x xs ih =>
      intro ys vs fm vals ⟨h, hlen⟩
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          obtain ⟨z, hz⟩ := optMmapSomeImpFupdateExistSome vs fm vals (x, y) h
          have := ih ys vs (fm.updateEq (x, y)) z ⟨hz, by simpa using hlen⟩
          have hl : (fm.updateListEq ((x, y) :: xs.zip ys)).lookup =
              ((fm.updateEq (x, y)).updateListEq (xs.zip ys)).lookup := rfl
          simp only [List.zip_cons_cons]
          rw [hl]
          exact this

/-- Exact HOL `opt_mmap_flookup_not_mem_domsub`
    (`crep_inlineProofScript.sml:1825-1831`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_flookup_not_mem_domsub"
  (fmap_as_finite_support_relation := [fm])]
theorem optMmapFlookupNotMemDomsub {α β : Type} [DecidableEq α] :
    ∀ (vs : List α) (fm : HolFiniteMapExact α β) (vals : List β) (x : α),
      vs.mapM fm.lookup = some vals ∧ x ∉ vs →
        vs.mapM (fm.eraseEq x).lookup = some vals := by
  intro vs fm vals x ⟨h, hx⟩
  rw [← h]
  refine OPT_MMAP_ALL_EQ _ _ vs (fun v hv => ?_)
  rw [lookup_eraseEq]
  have : v ≠ x := fun heq => hx (heq ▸ hv)
  simp [FDOMSUB_HOL, this]

/-- Exact HOL `opt_mmap_update_locals_not_vars_eval_eq`
    (`crep_inlineProofScript.sml:1843-1849`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_update_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem optMmapUpdateLocalsNotVarsEvalEq {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (n : Nat) (vs : List (HolWordLab width))
      (w : HolWordLab width) (s : CrepSemHOLState width σ),
      n ∉ (es.map crepExpVarsHOL).flatten ∧ es.mapM (evalCrepSemHOLExp s) = some vs →
        es.mapM (evalCrepSemHOLExp { s with locals := s.locals.updateEq (n, w) }) = some vs := by
  intro es n vs w s ⟨hn, h⟩
  rw [← h]
  refine OPT_MMAP_ALL_EQ _ _ es (fun e he => ?_)
  have hfresh : n ∉ crepExpVarsHOL e := fun hm =>
    hn (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, hm⟩)
  exact evalCrepSemHOLExp_updateLocals_eq_of_not_vars s e n w hfresh

/-- Exact HOL `evaluate_nested_seq_assign` (`crep_inlineProofScript.sml:1851-1873`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_nested_seq_assign"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evaluateNestedSeqAssign {width : Nat} [NeZero width] {σ : Type} :
    ∀ (ns : List Nat) (s : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
      (ws vals : List (HolWordLab width)),
      es.mapM (evalCrepSemHOLExp s) = some ws ∧
        (∀ x, x ∈ ns → x ∉ (es.map crepExpVarsHOL).flatten) ∧
        ns.mapM s.locals.lookup = some vals ∧
        ns.length = ws.length ∧
        ns.Nodup →
      ∃ s', evalCrepSemHOLProgExact s (crepNestedSeqHOL (panMap2 CrepProgHOL.assign ns es)) =
          (none, s') ∧
        crepInlineStateRelExact s s' ∧
        (∀ x, x ∉ ns → s'.locals.lookup x = s.locals.lookup x) ∧
        ns.mapM s'.locals.lookup = some ws := by
  intro ns
  induction ns with
  | nil =>
      intro s es ws vals ⟨hes, _, _, hlen, _⟩
      cases ws with
      | cons _ _ => simp at hlen
      | nil =>
          refine ⟨s, ?_, ?_, fun _ _ => rfl, rfl⟩
          · simp only [panMap2, crepNestedSeqHOL]
            exact evalCrepSemHOLProgExact_skip s
          · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons n ns ih =>
      intro s es ws vals ⟨hes, hfresh, hvals, hlen, hnodup⟩
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          cases es with
          | nil => simp at hes
          | cons e es =>
              simp only [List.mapM_cons] at hes hvals
              cases he : evalCrepSemHOLExp s e with
              | none => simp [he] at hes
              | some w' =>
                  cases hrest : es.mapM (evalCrepSemHOLExp s) with
                  | none => simp [he, hrest] at hes
                  | some ws' =>
                      simp [he, hrest] at hes
                      obtain ⟨hw, hws⟩ := hes
                      rw [hw] at he
                      rw [hws] at hrest
                      cases hn : s.locals.lookup n with
                      | none => simp [hn] at hvals
                      | some v0 =>
                          cases hns : ns.mapM s.locals.lookup with
                          | none => simp [hn, hns] at hvals
                          | some vals' =>
                              have hnodup' := List.nodup_cons.1 hnodup
                              have hn_es : n ∉ (es.map crepExpVarsHOL).flatten := by
                                intro hm
                                apply hfresh n (List.mem_cons_self)
                                simp only [List.map_cons, List.flatten_cons, List.mem_append]
                                exact Or.inr hm
                              let s1 : CrepSemHOLState width σ :=
                                CrepSemHOLState.setVar n w s
                              have hes1 : es.mapM (evalCrepSemHOLExp s1) = some ws :=
                                optMmapUpdateLocalsNotVarsEvalEq es n ws w s ⟨hn_es, hrest⟩
                              obtain ⟨vals1, hvals1⟩ :=
                                optMmapSomeImpFupdateExistSome ns s.locals vals' (n, w) hns
                              obtain ⟨s', hev, hrel, hframe, hlook⟩ :=
                                ih s1 es ws vals1
                                  ⟨hes1,
                                   (fun x hx hm => hfresh x (List.mem_cons_of_mem _ hx)
                                     (by simp only [List.map_cons, List.flatten_cons,
                                           List.mem_append]; exact Or.inr hm)),
                                   hvals1, by simpa using hlen, hnodup'.2⟩
                              have hassign : evalCrepSemHOLProgExact s
                                  (CrepProgHOL.assign n e) = (none, s1) := by
                                rw [evalCrepSemHOLProgExact_assign, crepExactEvalExp_eq_eval,
                                  he, hn]
                              refine ⟨s', ?_, ?_, ?_, ?_⟩
                              · simp only [panMap2, crepNestedSeqHOL]
                                rw [evalCrepSemHOLProgExact_seq_fixClockFree, hassign]
                                exact hev
                              · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
                                exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
                              · intro x hx
                                rw [hframe x (fun hm => hx (List.mem_cons_of_mem _ hm))]
                                have hxn : x ≠ n := fun heq => hx (heq ▸ List.mem_cons_self)
                                show FUPDATE_HOL s.locals.lookup (n, w) x = _
                                simp [FUPDATE_HOL, hxn]
                              · simp only [List.mapM_cons]
                                rw [hframe n hnodup'.1, hlook]
                                show (do let a ← FUPDATE_HOL s.locals.lookup (n, w) n
                                         let as ← some ws
                                         pure (a :: as)) = some (w :: ws)
                                simp [FUPDATE_HOL]

/-- Exact HOL `evaluate_nested_seq_assign_drule` (`crep_inlineProofScript.sml:1875-1891`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_nested_seq_assign_drule"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evaluateNestedSeqAssignDrule {width : Nat} [NeZero width] {σ : Type} :
    ∀ (ns : List Nat) (s : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
      (ws vals : List (HolWordLab width)) (r : Option (CrepResultHOLExact width))
      (s' : CrepSemHOLState width σ),
      es.mapM (evalCrepSemHOLExp s) = some ws ∧
        (∀ x, x ∈ ns → x ∉ (es.map crepExpVarsHOL).flatten) ∧
        ns.mapM s.locals.lookup = some vals ∧
        ns.length = ws.length ∧
        ns.Nodup ∧
        evalCrepSemHOLProgExact s (crepNestedSeqHOL (panMap2 CrepProgHOL.assign ns es)) =
          (r, s') →
      r = none ∧
        crepInlineStateRelExact s s' ∧
        (∀ x, x ∉ ns → s'.locals.lookup x = s.locals.lookup x) ∧
        ns.mapM s'.locals.lookup = some ws := by
  intro ns s es ws vals r s' ⟨hes, hfresh, hvals, hlen, hnodup, hev⟩
  obtain ⟨s'', hev', hrel, hframe, hlook⟩ :=
    evaluateNestedSeqAssign ns s es ws vals ⟨hes, hfresh, hvals, hlen, hnodup⟩
  rw [hev'] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  exact ⟨rfl, hrel, hframe, hlook⟩

end CrepInlineNestedSeqAssign

end Flapjack
