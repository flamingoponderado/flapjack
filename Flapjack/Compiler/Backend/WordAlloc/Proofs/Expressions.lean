import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LiveExpressions

namespace Flapjack.WordAlloc

namespace ExpressionWitnesses

/-- Canonical imported state roundtrip for the expression simulation. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end ExpressionWitnesses

/-- Flapjack list infrastructure: transport only successful argument results. -/
private theorem theWordsMapOf {width : Nat} [NeZero width] {α : Type}
    (f g : α → Option (WordLocW width)) :
    ∀ (l : List α), (∀ a ∈ l, ∀ v, f a = some v → g a = some v) →
      ∀ ws, theWords (l.map f) = some ws → theWords (l.map g) = some ws
  | [], _, ws, h => by simpa [theWords] using h
  | a :: l, hfg, ws, h => by
      simp only [List.map_cons, theWords] at h ⊢
      split at h
      · rename_i x xs hx hxs
        rw [hfg a (List.mem_cons_self ..) _ hx,
          theWordsMapOf f g l (fun b hb => hfg b (List.mem_cons_of_mem _ hb)) xs hxs]
        exact h
      · cases h

private theorem attachMapEq {α β : Type} (l : List α) (f : α → β) :
    (l.attach.map fun (x : { x // x ∈ l }) => f x.1) = l.map f := by
  simp

/-- Recursive proof infrastructure following HOL word_exp_ind. -/
private theorem applyColourExpAux {width : Nat} [NeZero width] {C F : Type}
    (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat)
    (hs : wordStateEqRel st cst) :
    ∀ (e : WordLangExpHOL (BitVec width)) (res : WordLocW width),
      WordSemStateFiniteExact.wordExp st e = some res →
      strongLocalsRel f (sptDomain (getLiveExp e)) st.locals cst.locals →
      WordSemStateFiniteExact.wordExp cst (applyColourExpCore f e) = some res
  | .const w, res, h, _ => by
      simpa [applyColourExpCore, WordSemStateFiniteExact.wordExp] using h
  | .var n, res, h, hr => by
      simp only [applyColourExpCore, WordSemStateFiniteExact.wordExp]
      apply strongLocalsRelGetVar f _ st cst n res
      exact ⟨hr, by
        simpa only [getLiveExp, sptMem] using
          (sptMem_sptInsert n n () .ln).mpr (Or.inl rfl), by
        simpa only [WordSemStateFiniteExact.wordExp] using h⟩
  | .lookup name, res, h, _ => by
      simpa [applyColourExpCore, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getStore, hs.2.1] using h
  | .load e, res, h, hr => by
      simp only [WordSemStateFiniteExact.wordExp] at h
      simp only [applyColourExpCore, WordSemStateFiniteExact.wordExp]
      split at h
      · rename_i w hw
        rw [applyColourExpAux st cst f hs e _ hw (by simpa only [getLiveExp] using hr)]
        simpa [WordSemStateFiniteExact.memLoad, hs.2.2.2.2.2.2.2.1,
          hs.2.2.2.2.2.2.2.2.1] using h
      · cases h
  | .op operator args, res, h, hr => by
      simp only [WordSemStateFiniteExact.wordExp] at h
      simp only [applyColourExpCore, WordSemStateFiniteExact.wordExp]
      rw [attachMapEq] at h
      rw [attachMapEq]
      rw [List.map_map]
      split at h
      · rename_i ws hws
        rw [theWordsMapOf (WordSemStateFiniteExact.wordExp st)
          (WordSemStateFiniteExact.wordExp cst ∘ applyColourExpCore f) args
          (fun a ha v hv => by
            have := List.sizeOf_lt_of_mem ha
            apply applyColourExpAux st cst f hs a v hv
            intro key value hk
            exact hr key value ⟨by simpa only [getLiveExp] using domainBigUnionSubset args a ha key hk.1, hk.2⟩) ws hws]
        exact h
      · cases h
  | .shift sh e n, res, h, hr => by
      simp only [WordSemStateFiniteExact.wordExp] at h
      simp only [applyColourExpCore, WordSemStateFiniteExact.wordExp]
      have he : strongLocalsRel f (sptDomain (getLiveExp e)) st.locals cst.locals := by
        intro key value hk
        exact hr key value ⟨by simpa [getLiveExp, sptDomain_sptUnion] using Or.inl hk.1, hk.2⟩
      have hn : strongLocalsRel f (sptDomain (getLiveExp n)) st.locals cst.locals := by
        intro key value hk
        exact hr key value ⟨by simpa [getLiveExp, sptDomain_sptUnion] using Or.inr hk.1, hk.2⟩
      split at h
      · rename_i w w1 hw hw1
        rw [applyColourExpAux st cst f hs e _ hw he,
          applyColourExpAux st cst f hs n _ hw1 hn]
        exact h
      · cases h
  termination_by e => sizeOf e

/-- Exact HOL successful expression-colouring simulation. Only source success,
the original state relation, and live-scoped local transport are premises. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "apply_colour_exp_lemma"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem applyColourExpLemma {width : Nat} [NeZero width] {C F : Type} :
    ∀ (st : WordSemStateFiniteExact width C F) (w : WordLangExpHOL (BitVec width))
      (cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (res : WordLocW width),
      WordSemStateFiniteExact.wordExp st w = some res ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLiveExp w)) st.locals cst.locals →
      WordSemStateFiniteExact.wordExp cst (applyColourExp f w) = some res := by
  rintro st w cst f res ⟨h, hs, hr⟩
  exact applyColourExpAux st cst f hs w res h hr

end Flapjack.WordAlloc
