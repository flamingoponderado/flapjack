import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.MoreAtoms

/-!
# crep_inline finite-map lemmas used by `inline_prog_correct[Nontail]`

Ports of `SUBMAP_IMP_FUPDATE_LIST_SUBMAP` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:143-150`,
bead `flapjack-pxn.18.5.5.42.6`) and `opt_mmap_flookup_some_then_same_fdom`
(`:501-509`, bead `.42.7`) over the finite-support carrier: `|++ ZIP` is
`updateListEq`, `SUBMAP` is `HolFiniteMapExact.submap`, `OPT_MMAP (FLOOKUP fm)`
is `List.mapM fm.lookup`, and `FDOM` equality is equality of `crepHolFdom` of
the lookups.
-/

namespace Flapjack.CrepInlineExact

/-- Exact HOL `SUBMAP_IMP_FUPDATE_LIST_SUBMAP` (`crep_inlineProofScript.sml:143-145`):
    `f SUBMAP g ∧ LENGTH x = LENGTH y ⇒ f |++ ZIP(x, y) SUBMAP g |++ ZIP(x, y)`.
    The length hypothesis is kept as in HOL, although the proof does not
    need it. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_FUPDATE_LIST_SUBMAP"
  (fmap_as_finite_support_relation := [f, g])]
theorem submapImpFupdateListSubmapExact {β : Type}
    (x : List Nat) (y : List β) (f : HolFiniteMapExact Nat β) (g : HolFiniteMapExact Nat β) :
    f.submap g ∧ x.length = y.length →
      (f.updateListEq (x.zip y)).submap (g.updateListEq (x.zip y)) := by
  rintro ⟨h, _⟩ k v hk
  simp only [HolFiniteMapExact.lookup_updateListEq] at hk ⊢
  exact submap_updateList _ _ _ h k v hk

/-- Exact HOL `opt_mmap_flookup_some_then_same_fdom`
    (`crep_inlineProofScript.sml:501-504`):
    `OPT_MMAP (FLOOKUP fm) vs = SOME vals ∧ LENGTH vs = LENGTH upd_vals ⇒
     FDOM (fm |++ ZIP(vs, upd_vals)) = FDOM fm`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_flookup_some_then_same_fdom"
  (fmap_as_finite_support_relation := [fm])]
theorem optMmapFlookupSomeThenSameFdomExact {β : Type}
    (vs : List Nat) (fm : HolFiniteMapExact Nat β) (vals upd_vals : List β) :
    vs.mapM fm.lookup = some vals ∧ vs.length = upd_vals.length →
      crepHolFdom (fm.updateListEq (vs.zip upd_vals)).lookup = crepHolFdom fm.lookup := by
  rintro ⟨hmap, -⟩
  have hdom : ∀ k, k ∈ vs → (fm.lookup k).isSome := by
    intro k hk
    induction vs generalizing vals with
    | nil => cases hk
    | cons a rest ih =>
        simp only [List.mapM_cons] at hmap
        cases ha : fm.lookup a with
        | none => rw [ha] at hmap; simp at hmap
        | some va =>
            rw [ha] at hmap
            cases hr : rest.mapM fm.lookup with
            | none => rw [hr] at hmap; simp at hmap
            | some vr =>
                rcases List.mem_cons.mp hk with rfl | hk'
                · rw [ha]; rfl
                · exact ih vr hr hk'
  funext k
  simp only [crepHolFdom, HolFiniteMapExact.lookup_updateListEq]
  apply dom_updateList
  intro e he
  exact hdom e.1 (List.of_mem_zip he).1

end Flapjack.CrepInlineExact
