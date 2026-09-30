import Flapjack.Pancake.Proofs.CrepInline.Expressions

/-!
# crep_inline: expression evaluation under `locals_rel` and `state_rel`

Counterparts of `cakeml/pancake/proofs/crep_inlineProofScript.sml:78-116`
(bead `flapjack-pxn.18.5.5.43.5.3`): `eval_original_extend_locals_rel`,
`eval_state_locals_rel` and `eval_optmmap_state_locals_rel`, derived as in HOL
from the ported `eval_original_extend_locals` and the record equality
`s with locals := t.locals = t` given by the ten `state_rel` fields.
-/

namespace Flapjack.CrepInlineExact

namespace ExpressionRelationsSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ExpressionRelationsSupport

/-- Local support: `state_rel s t` gives `s with locals := t.locals = t`
    (HOL `state_component_equality`). -/
private theorem withLocals_eq_of_stateRel {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} (h : crepInlineStateRelExact s t) :
    ({ s with locals := t.locals } : CrepSemHOLState width σ) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  cases s; cases t
  simp_all

/-- Exact HOL `eval_original_extend_locals_rel` (`crep_inlineProofScript.sml:78-91`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_original_extend_locals_rel"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evalOriginalExtendLocalsRelExact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width) (wl : HolWordLab width)
      (t : CrepSemHOLState width σ),
      evalCrepSemHOLExp s e = some wl →
        crepInlineLocalsRelExact s t ∧ crepInlineStateRelExact s t →
        evalCrepSemHOLExp t e = some wl := by
  intro s e wl t heval ⟨hloc, hrel⟩
  have h := evalOriginalExtendLocalsExact s e wl t.locals heval hloc
  rwa [withLocals_eq_of_stateRel hrel] at h

/-- Exact HOL `eval_state_locals_rel` (`crep_inlineProofScript.sml:93-102`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_state_locals_rel"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evalStateLocalsRelExact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width) (wl : HolWordLab width)
      (t : CrepSemHOLState width σ),
      evalCrepSemHOLExp s e = some wl ∧ crepInlineStateRelExact s t ∧
        crepInlineLocalsRelExact s t →
        evalCrepSemHOLExp t e = some wl :=
  fun s e wl t ⟨h, hrel, hloc⟩ => evalOriginalExtendLocalsRelExact s e wl t h ⟨hloc, hrel⟩

/-- Exact HOL `eval_optmmap_state_locals_rel` (`crep_inlineProofScript.sml:105-116`);
    `OPT_MMAP` is `List.mapM`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_optmmap_state_locals_rel"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evalOptmmapStateLocalsRelExact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
      (ws : List (HolWordLab width)) (t : CrepSemHOLState width σ),
      es.mapM (evalCrepSemHOLExp s) = some ws ∧ crepInlineStateRelExact s t ∧
        crepInlineLocalsRelExact s t →
        es.mapM (evalCrepSemHOLExp t) = some ws := by
  intro s es
  induction es with
  | nil => intro ws t ⟨h, _, _⟩; exact h
  | cons e es ih =>
      intro ws t ⟨h, hrel, hloc⟩
      simp only [List.mapM_cons] at h ⊢
      cases he : evalCrepSemHOLExp s e with
      | none => simp [he] at h
      | some w =>
          cases hr : es.mapM (evalCrepSemHOLExp s) with
          | none => simp [he, hr] at h
          | some ws' =>
              simp only [he, hr, Option.bind_eq_bind, Option.bind_some] at h
              rw [evalStateLocalsRelExact s e w t ⟨he, hrel, hloc⟩,
                ih ws' t ⟨hr, hrel, hloc⟩]
              exact h

end Flapjack.CrepInlineExact
