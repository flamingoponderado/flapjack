module

public import Mathlib.Data.Set.Basic
public import Flapjack.FiniteMap.AlistExact
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Pancake.Proofs.CrepInline

@[expose] public section

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

/-- Local support: pointwise `SUBMAP` is preserved by the same `|++`. -/
theorem submap_fupdateListHOL {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (f g : α → Option β),
      (∀ k v, f k = some v → g k = some v) →
      ∀ k v, FUPDATE_LIST_HOL f entries k = some v → FUPDATE_LIST_HOL g entries k = some v
  | [], _, _, h => h
  | e :: es, f, g, h => by
      simp only [FUPDATE_LIST_HOL_cons]
      refine submap_fupdateListHOL es _ _ (fun k v hk => ?_)
      simp only [FUPDATE_HOL] at hk ⊢
      by_cases hke : k = e.1
      · simp_all
      · simp only [hke, if_false] at hk ⊢; exact h k v hk

/-- Local support: `|++` over keys already in the domain keeps the domain. -/
theorem dom_fupdateListHOL {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (f : α → Option β),
      (∀ e ∈ entries, (f e.1).isSome) →
      ∀ k, (FUPDATE_LIST_HOL f entries k).isSome = (f k).isSome
  | [], _, _, _ => rfl
  | e :: es, f, h, k => by
      simp only [FUPDATE_LIST_HOL_cons]
      rw [dom_fupdateListHOL es _ (fun e' he' => ?_) k]
      · simp only [FUPDATE_HOL]
        by_cases hke : k = e.1
        · subst hke; simp [h e List.mem_cons_self]
        · simp [hke]
      · simp only [FUPDATE_HOL]
        by_cases hke : e'.1 = e.1
        · simp [hke]
        · simp only [hke, if_false]; exact h e' (List.mem_cons_of_mem _ he')

open Classical in
/-- Exact HOL `SUBMAP_IMP_FUPDATE_LIST_SUBMAP` (`crep_inlineProofScript.sml:143-145`):
    `f SUBMAP g ∧ LENGTH x = LENGTH y ⇒ f |++ ZIP(x, y) SUBMAP g |++ ZIP(x, y)`,
    polymorphic in the key and value types as in HOL; `|++` uses HOL's
    (classical) key equality, so no decidability binder is exposed.  The length hypothesis is kept
    as in HOL, although the proof does not need it. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_FUPDATE_LIST_SUBMAP"
  (fmap_as_finite_support_relation := [f, g])]
theorem submapImpFupdateListSubmapExact {α β : Type}
    (x : List α) (y : List β) (f : HolFiniteMapExact α β) (g : HolFiniteMapExact α β) :
    f.submap g ∧ x.length = y.length →
      (f.updateListEq (x.zip y)).submap (g.updateListEq (x.zip y)) := by
  rintro ⟨h, _⟩ k v hk
  simp only [HolFiniteMapExact.lookup_updateListEq] at hk ⊢
  exact submap_fupdateListHOL _ _ _ h k v hk

open Classical in
/-- Exact HOL `opt_mmap_flookup_some_then_same_fdom`
    (`crep_inlineProofScript.sml:501-504`):
    `OPT_MMAP (FLOOKUP fm) vs = SOME vals ∧ LENGTH vs = LENGTH upd_vals ⇒
     FDOM (fm |++ ZIP(vs, upd_vals)) = FDOM fm`, polymorphic in the key and
    value types as in HOL, with classical key equality in `|++`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_flookup_some_then_same_fdom"
  (fmap_as_finite_support_relation := [fm])]
theorem optMmapFlookupSomeThenSameFdomExact {α β : Type}
    (vs : List α) (fm : HolFiniteMapExact α β) (vals upd_vals : List β) :
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
  apply dom_fupdateListHOL
  intro e he
  exact hdom e.1 (List.of_mem_zip he).1

/-! ## Exact `FDOM`/`SUBMAP` ports over the canonical domain and submap

    `HolFiniteMapExact.domain` (`Flapjack/FiniteMap/DomainExact.lean`) renders
    HOL's `FDOM` as a set of keys and `HolFiniteMapExact.submap`
    (`Flapjack/FiniteMap/SubmapExact.lean`) renders HOL's `SUBMAP`; the typed
    captures keep HOL's independent value types on the two map arguments. -/

/-- Pointwise form of the `FDOM` equality characterization used by HOL
    `fdom_eq_flookup_thm`; the two options may have different value types.
    Flapjack infrastructure, no separate HOL original. -/
theorem optionNeNoneIffEq {β γ : Type} (a : Option β) (b : Option γ) :
    (a ≠ none ↔ b ≠ none) ↔
      ((∃ v : β, a = some v) → ∃ v : γ, b = some v) ∧ (a = none → b = none) := by
  cases a <;> cases b <;> simp

/-- Pointwise form of the `FDOM` subset characterization used by HOL
    `fdom_subset_flookup_thm`; the two options may have different value types.
    Flapjack infrastructure, no separate HOL original. -/
theorem optionNeNoneImpEq {β γ : Type} (a : Option β) (b : Option γ) :
    (a ≠ none → b ≠ none) ↔ ((∃ p : β, a = some p) → ∃ q : γ, b = some q) := by
  cases a <;> cases b <;> simp

/-- Exact HOL `fdom_eq_flookup_thm` (`crep_inlineProofScript.sml:784`):
    `FDOM f1 = FDOM f2` exactly when every key bound in `f1` is bound in `f2`
    and every key unbound in `f1` is unbound in `f2`. `FDOM` is the canonical
    domain set; the two maps keep HOL's independent value types. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_eq_flookup_thm"
  (fmap_as_finite_support_relation := [f1, f2])]
theorem fdomEqFlookupExact {α β γ : Type} (f1 : HolFiniteMapExact α β)
    (f2 : HolFiniteMapExact α γ) :
    f1.domain = f2.domain ↔
      ((∀ x, (∃ v : β, f1.lookup x = some v) → ∃ v : γ, f2.lookup x = some v) ∧
        (∀ x, f1.lookup x = none → f2.lookup x = none)) := by
  have pointwise : ∀ x, (f1.lookup x ≠ none ↔ f2.lookup x ≠ none) ↔
      ((∃ v : β, f1.lookup x = some v) → ∃ v : γ, f2.lookup x = some v) ∧
        (f1.lookup x = none → f2.lookup x = none) := fun x => optionNeNoneIffEq _ _
  constructor
  · intro h
    have hmem : ∀ x, f1.lookup x ≠ none ↔ f2.lookup x ≠ none := by
      intro x
      have := Set.ext_iff.mp h x
      simpa [HolFiniteMapExact.domain] using this
    exact ⟨fun x hx => ((pointwise x).mp (hmem x)).1 hx,
      fun x hx => ((pointwise x).mp (hmem x)).2 hx⟩
  · intro hpair
    ext x
    simpa [HolFiniteMapExact.domain] using (pointwise x).mpr ⟨hpair.1 x, hpair.2 x⟩

/-- Exact HOL `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`):
    `FDOM f ⊆ FDOM g` exactly when every binding of `f` has a binding of `g`
    at the same key. The two maps keep HOL's independent value types. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_subset_flookup_thm"
  (fmap_as_finite_support_relation := [f, g])]
theorem fdomSubsetFlookupExact {α β γ : Type} (f : HolFiniteMapExact α β)
    (g : HolFiniteMapExact α γ) :
    f.domain ⊆ g.domain ↔
      (∀ x p, f.lookup x = some p → ∃ q : γ, g.lookup x = some q) := by
  simp only [HolFiniteMapExact.domain, Set.mem_ofPred_eq, Set.subset_def]
  constructor
  · intro h x p hp
    exact Option.isSome_iff_exists.mp ((Option.ne_none_iff_isSome (o := g.lookup x)).mp
      (h x (by rw [hp]; exact Option.some_ne_none p)))
  · intro h x hne
    obtain ⟨p, hp⟩ :=
      Option.isSome_iff_exists.mp ((Option.ne_none_iff_isSome (o := f.lookup x)).mp hne)
    obtain ⟨q, hq⟩ := h x p hp
    rw [hq]
    exact Option.some_ne_none q

/-- Exact HOL `fdoms_eq_opt_mmap_flookup_some` (`crep_inlineProofScript.sml:1833`):
    equal domains and a successful `OPT_MMAP (FLOOKUP fm) vs` give a successful
    `OPT_MMAP (FLOOKUP fm') vs`. The value types of the two maps stay
    independent, so the witness list has the second map's value type. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdoms_eq_opt_mmap_flookup_some"
  (fmap_as_finite_support_relation := [fm, fm'])]
theorem fdomsEqOptMmapFlookupSomeExact {α β γ : Type} (vs : List α)
    (fm : HolFiniteMapExact α β) (fm' : HolFiniteMapExact α γ) (vals : List β) :
    fm.domain = fm'.domain ∧ vs.mapM fm.lookup = some vals →
      ∃ z : List γ, vs.mapM fm'.lookup = some z := by
  rintro ⟨hdom, hmap⟩
  have hsrc : ∀ e, e ∈ vs → ∃ y : β, fm.lookup e = some y :=
    (OPT_MMAP_SOME_ALL fm.lookup vs).mp ⟨vals, hmap⟩
  refine (OPT_MMAP_SOME_ALL fm'.lookup vs).mpr ?_
  intro e he
  obtain ⟨y, hy⟩ := hsrc e he
  have hmem : e ∈ fm'.domain := by
    rw [← hdom]
    simp [HolFiniteMapExact.domain, hy]
  simp only [HolFiniteMapExact.domain, Set.mem_ofPred_eq] at hmem
  exact Option.isSome_iff_exists.mp ((Option.ne_none_iff_isSome (o := fm'.lookup e)).mp hmem)

/-- Exact HOL `opt_mmap_some_then_subset_fdom` (`crep_inlineProofScript.sml:175`):
    a successful `OPT_MMAP (FLOOKUP fm) vs` puts every element of `vs` in
    `FDOM fm`. HOL's `set vs` is the list's element set, so Lean states the
    same subset with the set comprehension `{v | v ∈ vs}`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_some_then_subset_fdom"
  (fmap_as_finite_support_relation := [fm])]
theorem optMmapSomeThenSubsetFdomExact {α β : Type} (vs : List α)
    (fm : HolFiniteMapExact α β) (vals : List β) :
    vs.mapM fm.lookup = some vals → {v | v ∈ vs} ⊆ fm.domain := by
  intro hmap
  have hsrc : ∀ e, e ∈ vs → ∃ y : β, fm.lookup e = some y :=
    (OPT_MMAP_SOME_ALL fm.lookup vs).mp ⟨vals, hmap⟩
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv
  obtain ⟨y, hy⟩ := hsrc v hv
  simp [HolFiniteMapExact.domain, hy]

open Classical in
/-- Exact HOL `res_var_submap_res_var` (`crep_inlineProofScript.sml:154`):
    `SUBMAP` is preserved by restoring the same `(key, value option)` entry.
    `res_var` is the canonical `resVarEq`; key equality is HOL equality, so no
    `DecidableEq` binder is exposed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "res_var_submap_res_var"
  (fmap_as_finite_support_relation := [f, g])]
theorem resVarSubmapResVarExact {α β : Type} (f : HolFiniteMapExact α β)
    (g : HolFiniteMapExact α β) (x : α) (y : Option β) :
    f.submap g →
      (HolFiniteMapExact.resVarEq f (x, y)).submap (HolFiniteMapExact.resVarEq g (x, y)) := by
  intro h k v hk
  cases y with
  | none =>
      simp only [HolFiniteMapExact.lookup_resVarEq_none] at hk ⊢
      by_cases same : k = x
      · rw [FDOMSUB_HOL, if_pos same] at hk
        exact absurd hk (by simp)
      · rw [FDOMSUB_HOL, if_neg same] at hk ⊢
        exact h k v hk
  | some yv =>
      simp only [HolFiniteMapExact.lookup_resVarEq_some] at hk ⊢
      by_cases same : k = x
      · rw [FUPDATE_HOL, if_pos same] at hk ⊢
        exact hk
      · rw [FUPDATE_HOL, if_neg same] at hk ⊢
        exact h k v hk

/-- A successful lookup in the canonical `alistToFmap` identifies an association
    listed in the source list. Flapjack local support for the HOL `ALOOKUP_MEM`
    step of `submap_flookup_alist_to_fmap`; no separate HOL original. -/
theorem mem_of_lookup_alistToFmap {α β : Type} (entries : List (α × β)) (key : α)
    (value : β) (found : (HolFiniteMapExact.alistToFmap entries).lookup key = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [HolFiniteMapExact.alistToFmap] at found
  | cons entry rest ih =>
      by_cases same : key = entry.1
      · rw [same] at found ⊢
        rw [HolFiniteMapExact.lookup_alistToFmap_head entry rest] at found
        have equal : value = entry.2 := (Option.some.inj found).symm
        exact List.mem_cons.mpr (Or.inl (by rw [equal]))
      · rw [HolFiniteMapExact.lookup_alistToFmap_tail entry rest key same] at found
        exact List.mem_cons_of_mem _ (ih found)

open Classical in
/-- Exact HOL `submap_flookup_alist_to_fmap` (`crep_inlineProofScript.sml:3070`):
    a submap of `alist_to_fmap t` can only bind associations that `t` lists.
    `alist_to_fmap` is the canonical `alistToFmap`; key equality is HOL
    equality, so no `DecidableEq` binder is exposed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "submap_flookup_alist_to_fmap"
  (fmap_as_finite_support_relation := [s])]
theorem submapFlookupAlistToFmapExact {α β : Type} (s : HolFiniteMapExact α β)
    (t : List (α × β)) (x : α) (v : β) :
    s.submap (HolFiniteMapExact.alistToFmap t) ∧ s.lookup x = some v → (x, v) ∈ t := by
  rintro ⟨hsub, hlookup⟩
  exact mem_of_lookup_alistToFmap t x v (hsub x v hlookup)

end Flapjack.CrepInlineExact
