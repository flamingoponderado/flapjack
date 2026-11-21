module

public import Flapjack.Pancake.Semantics.PanCommonProps
public import Flapjack.Pancake.Semantics.CrepSem.HOLState
public import Flapjack.Misc.Option
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# Exact finite-map carriers for `pan_commonProps`

The `pan_commonPropsScript.sml` context predicates `ctxt_max`/`no_overlap` and
the `update_eq_zip_flookup` lemma are stated over HOL `|->` finite maps.  Their
Lean twins below use the reviewed canonical `HolFiniteMapExact` translation and
record the standalone map parameters with
`fmap_as_finite_support_parameters`.  The raw-function helpers in
`PanCommonProps.lean` stay for the production-carrier proofs; these exact twins
are the reviewed ports of the HOL declarations.
-/

namespace Flapjack

/-- Broad lookup projection for the witness roundtrip; Flapjack infrastructure. -/
def holFiniteMaptoBroadlookup {κ β : Type}
    (fm : HolFiniteMapExact κ β) : κ → Option β := fm.lookup

/-- Reconstruct the canonical carrier from a broad lookup and support proof. -/
def holFiniteMapofBroad {κ β : Type} (lookup : κ → Option β)
    (finiteSupport : ∃ keys : List κ, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact κ β := ⟨lookup, finiteSupport⟩

/-- Canonical standalone-map witness for the exact `ctxt_max_def` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_ctxtMaxHOL_fm {α β : Type}
    (fm : HolFiniteMapExact α (β × List Nat)) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Canonical standalone-map witness for the exact `no_overlap_def` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_noOverlapHOL_fm {α β γ : Type}
    (fm : HolFiniteMapExact α (β × List γ)) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Canonical standalone-map witness for the exact `update_eq_zip_flookup`
    parameter. -/
theorem holFmapAsFiniteSupportParamWitness_updateEqZipFlookupExactHOL_f
    {α β : Type} (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Exact port of HOL `pan_commonProps$ctxt_max_def`
    (`pan_commonPropsScript.sml:8-14`).  The typed capture in
    `pan_common_props_finite_map_probe.out` gives `∀(n :num) (fm :α |-> β # num
    list), ctxt_max n fm ⇔ 0 ≤ n ∧ ∀ v a xs, FLOOKUP fm v = SOME (a,xs) ⇒ ∀ x,
    MEM x xs ⇒ x ≤ n`.  The map is the canonical finite-support translation and
    is recorded as a bare parameter entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "ctxt_max_def"
  (fmap_as_finite_support_parameters := [fm])]
def ctxtMaxHOL {α β : Type} (n : Nat) (fm : HolFiniteMapExact α (β × List Nat)) : Prop :=
  0 ≤ n ∧ ∀ (v : α) (a : β) (xs : List Nat),
    fm.lookup v = some (a, xs) → ∀ x ∈ xs, x ≤ n

/-- Flapjack-only support: HOL `no_overlap_def`'s negated disjointness premise
    implies the shared-slot existential used by the finite-map lookup proofs. -/
theorem notListDisjointExists {γ : Type} (xs ys : List γ)
    (h : ¬ ListDisjoint xs ys) : ∃ z, z ∈ xs ∧ z ∈ ys := by
  exact Classical.byContradiction (fun hnone =>
    h (fun z hx hy => hnone ⟨z, hx, hy⟩))

/-- Exact port of HOL `pan_commonProps$no_overlap_def`
    (`pan_commonPropsScript.sml:18-24`).  The typed capture gives
    `∀(fm :α |-> β # γ list), no_overlap fm ⇔ (∀ x a xs, FLOOKUP fm x = SOME
    (a,xs) ⇒ ALL_DISTINCT xs) ∧ ∀ x y a b xs ys, FLOOKUP fm x = SOME (a,xs) ∧
    FLOOKUP fm y = SOME (b,ys) ∧ ¬DISJOINT (set xs) (set ys) ⇒ x = y`.  HOL's
    `¬DISJOINT (set xs) (set ys)` is kept as the negated `ListDisjoint` premise;
    the untagged `notListDisjointExists` derives the shared-slot existential for
    the lookup proofs.  `ALL_DISTINCT` is `Nodup`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "no_overlap_def"
  (fmap_as_finite_support_parameters := [fm])]
def noOverlapHOL {α β γ : Type} (fm : HolFiniteMapExact α (β × List γ)) : Prop :=
  (∀ (x : α) (a : β) (xs : List γ), fm.lookup x = some (a, xs) → xs.Nodup) ∧
    ∀ (x y : α) (a b : β) (xs ys : List γ),
      fm.lookup x = some (a, xs) ∧ fm.lookup y = some (b, ys) ∧
        ¬ ListDisjoint xs ys → x = y

/-- HOL-equality update of a lookup list; local to the exact `|++` rendering. -/
private theorem lookup_FUPDATE_LIST_HOL_not_mem [DecidableEq α] (f : FiniteMap α β)
    (entries : List (α × β)) (a : α) (h : a ∉ entries.map Prod.fst) :
    FUPDATE_LIST_HOL f entries a = f a := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry rest ih =>
      rw [FUPDATE_LIST_HOL_cons]
      have hne : entry.1 ≠ a := by
        intro heq
        exact h (by simp [heq])
      have hrest : a ∉ rest.map Prod.fst := by
        intro hmem
        exact h (by simp [hmem])
      rw [ih (FUPDATE_HOL f entry) hrest]
      simp [FUPDATE_HOL, Ne.symm hne]

/-- Exact port of HOL `pan_commonProps$update_eq_zip_flookup`
    (`pan_commonPropsScript.sml:244-251`).  The typed capture gives
    `∀(xs :α list) (f :α |-> β) (ys :β list) (n :num), ALL_DISTINCT xs ∧ LENGTH
    xs = LENGTH ys ∧ n < LENGTH xs ⇒ FLOOKUP (f |++ ZIP (xs,ys)) xs❲n❳ = SOME
    ys❲n❳`, with zero hypotheses.  `f |++` is `updateListEq`, `FLOOKUP` is
    `.lookup`, and the indexed `EL` is `getElem`; the map is a bare parameter
    entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "update_eq_zip_flookup"
  (fmap_as_finite_support_parameters := [f])]
theorem updateEqZipFlookupExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (f : HolFiniteMapExact α β) (ys : List β) (n : Nat)
    (h : xs.Nodup ∧ xs.length = ys.length ∧ n < xs.length) :
    (f.updateListEq (xs.zip ys)).lookup (xs[n]'h.2.2) =
      some (ys[n]'(by
                    rw [← h.2.1]
                    exact h.2.2)) := by
  obtain ⟨hdistinct, hlen, hn⟩ := h
  show (f.updateListEq (xs.zip ys)).lookup (xs[n]'hn) =
      some (ys[n]'(by
                    rw [← hlen]
                    exact hn))
  induction xs generalizing f ys n with
  | nil => simp at hn
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          rw [List.nodup_cons] at hdistinct
          obtain ⟨ha, hdistinctTail⟩ := hdistinct
          have hlenTail : xs.length = ys.length := by simpa using hlen
          cases n with
          | zero =>
              simp only [List.getElem_cons_zero]
              rw [List.zip_cons_cons, HolFiniteMapExact.lookup_updateListEq,
                FUPDATE_LIST_HOL_cons]
              rw [lookup_FUPDATE_LIST_HOL_not_mem (FUPDATE_HOL f.lookup (a, y))
                (xs.zip ys) a (by
                                rw [List.map_fst_zip (by omega)]
                                exact ha)]
              simp [FUPDATE_HOL]
          | succ k =>
              have hk : k < xs.length := by
                simp only [List.length_cons] at hn
                omega
              simp only [List.getElem_cons_succ]
              rw [List.zip_cons_cons, HolFiniteMapExact.lookup_updateListEq,
                FUPDATE_LIST_HOL_cons]
              have hstep := ih (f.updateEq (a, y)) ys k hdistinctTail hlenTail hk
              simp only [HolFiniteMapExact.lookup_updateListEq] at hstep
              exact hstep


/-- Canonical standalone-map witness for the exact `opt_mmap_some_eq_zip_flookup`
    parameter. -/
theorem holFmapAsFiniteSupportParamWitness_optMmapSomeEqZipFlookupExactHOL_f
    {α β : Type} (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Exact port of HOL `pan_commonProps$opt_mmap_some_eq_zip_flookup`
    (`pan_commonPropsScript.sml:170-176`): `∀ xs f ys, ALL_DISTINCT xs ∧
    LENGTH xs = LENGTH ys ⇒ OPT_MMAP (FLOOKUP (f |++ ZIP (xs,ys))) xs =
    SOME ys`.  `f |++` is `updateListEq`, `OPT_MMAP` is `List.mapM`,
    `FLOOKUP` is `.lookup`, and the map is a bare parameter entry.  Binder
    order and the single conjunctive premise follow HOL. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_some_eq_zip_flookup"
  (fmap_as_finite_support_parameters := [f])]
theorem optMmapSomeEqZipFlookupExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (f : HolFiniteMapExact α β) (ys : List β)
    (h : xs.Nodup ∧ xs.length = ys.length) :
    xs.mapM (fun key => (f.updateListEq (xs.zip ys)).lookup key) = some ys := by
  obtain ⟨hdistinct, hlen⟩ := h
  have hraw := opt_mmap_some_eq_zip_flookup (α := α) (β := β) xs f.lookup ys
    hdistinct hlen
  simpa only [HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL_eq_FUPDATE_LIST, FLOOKUP] using hraw

/-- Canonical standalone-map witness for the exact `opt_mmap_disj_zip_flookup`
    parameter. -/
theorem holFmapAsFiniteSupportParamWitness_optMmapDisjZipFlookupExactHOL_f
    {α β : Type} (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Exact port of HOL `pan_commonProps$opt_mmap_disj_zip_flookup`
    (`pan_commonPropsScript.sml:188-194`): `∀ xs f ys zs, distinct_lists xs ys
    ∧ LENGTH xs = LENGTH zs ⇒ OPT_MMAP (FLOOKUP (f |++ ZIP (xs,zs))) ys =
    OPT_MMAP (FLOOKUP f) ys`.  HOL's Boolean `distinct_lists` is the tagged
    `distinctListsHol`; `f |++` is `updateListEq`, `OPT_MMAP` is `List.mapM`,
    and the map is a bare parameter entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_disj_zip_flookup"
  (fmap_as_finite_support_parameters := [f])]
theorem optMmapDisjZipFlookupExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (f : HolFiniteMapExact α β) (ys : List α) (zs : List β)
    (h : distinctListsHol xs ys = true ∧ xs.length = zs.length) :
    ys.mapM (fun key => (f.updateListEq (xs.zip zs)).lookup key) =
      ys.mapM (fun key => f.lookup key) := by
  obtain ⟨hdisj, hlen⟩ := h
  have hraw := opt_mmap_disj_zip_flookup (α := α) (β := β) xs f.lookup ys zs
    ((distinctListsHol_eq_true_iff_listDisjoint xs ys).mp hdisj) hlen
  simpa only [HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL_eq_FUPDATE_LIST, FLOOKUP] using hraw

/-! ## Remaining `pan_commonProps` finite-map lemmas

These port the HOL declarations that were listed as open in
`PanCommonProps.lean`'s module note, plus the map-valued lemmas whose carriers
are finite maps.  Every statement uses the canonical `HolFiniteMapExact`
carrier, HOL equality (`DecidableEq`) for `|+`, `|++` and `\\`, and the typed
captures in `pan_common_props_exact_map_probe.out`.
-/

/-- Flapjack infrastructure: the canonical carrier is determined by its lookup
    function, because the finite-support field is a proposition. -/
theorem HolFiniteMapExact.ext {α β : Type} {m n : HolFiniteMapExact α β}
    (h : m.lookup = n.lookup) : m = n := by
  cases m with
  | mk lm pm =>
    cases n with
    | mk ln pn =>
      simp only at h
      subst h
      rfl

/-- A list of updates whose every value is `m` binds `some m` at any key that
    occurs in it, whatever the order of the entries. -/
theorem FLOOKUP_FUPDATE_LIST_HOL_of_all_value [DecidableEq α]
    (f : FiniteMap α β) (entries : List (α × β)) (m : β)
    (hall : ∀ entry ∈ entries, entry.2 = m) (key : α)
    (hkey : key ∈ entries.map Prod.fst) :
    FLOOKUP (FUPDATE_LIST_HOL f entries) key = some m := by
  induction entries generalizing f with
  | nil => simp at hkey
  | cons entry entries ih =>
      rw [FUPDATE_LIST_HOL_cons]
      by_cases hmem : key ∈ entries.map Prod.fst
      · exact ih (FUPDATE_HOL f entry)
          (fun e he => hall e (by simp [he])) hmem
      · have hkey' : key = entry.1 := by
          rw [List.map_cons, List.mem_cons] at hkey
          rcases hkey with h | h
          · exact h
          · exact absurd h hmem
        subst hkey'
        rw [FLOOKUP_FUPDATE_LIST_HOL_not_mem]
        · rw [FLOOKUP_FUPDATE_HOL]
          rw [if_pos rfl]
          rw [hall entry (by simp)]
        · exact hmem

/-- Domain subtraction commutes past a list of updates that omits the key,
    for HOL equality (`\\`). -/
theorem FDOMSUB_HOL_FUPDATE_LIST_HOL_commutes [DecidableEq α]
    (f : FiniteMap α β) (entries : List (α × β)) (x : α)
    (h : x ∉ entries.map Prod.fst) :
    FDOMSUB_HOL (FUPDATE_LIST_HOL f entries) x =
      FUPDATE_LIST_HOL (FDOMSUB_HOL f x) entries := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
      have hne : x ≠ entry.1 := fun he => h (by simp [he])
      have htail : x ∉ entries.map Prod.fst := fun hm => h (by simp [hm])
      rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
      rw [ih (FUPDATE_HOL f entry) htail]
      rw [FDOMSUB_HOL_FUPDATE_HOL_neq f x entry.1 entry.2 hne]

/-- Canonical standalone-map witness for the exact `opt_mmap_flookup_update`
    parameter. -/
theorem holFmapAsFiniteSupportParamWitness_optMmapFlookupUpdateExactHOL_fm
    {α β : Type} (fm : HolFiniteMapExact β α) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `pan_commonProps$opt_mmap_flookup_update`
    (`pan_commonPropsScript.sml:156-161`).  The typed capture gives
    `OPT_MMAP (FLOOKUP (fm :β |-> α)) (xs :β list) = SOME (ys :α list) ∧
    ¬MEM (x :β) xs ⇒ OPT_MMAP (FLOOKUP fm⟨x ↦ (y :α)⟩) xs = SOME ys`.
    `|+` is `updateEq`, `OPT_MMAP` is `List.mapM` applied to the partially
    applied lookup `fm.lookup` / `(fm.updateEq (x, y)).lookup`, and the map is a
    bare parameter entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_flookup_update"
  (fmap_as_finite_support_parameters := [fm])]
theorem optMmapFlookupUpdateExactHOL {α β : Type} [DecidableEq β]
    (fm : HolFiniteMapExact β α) (xs : List β) (ys : List α) (x : β) (y : α)
    (h : xs.mapM fm.lookup = some ys ∧ x ∉ xs) :
    xs.mapM (fm.updateEq (x, y)).lookup = some ys := by
  obtain ⟨hm, hx⟩ := h
  have hcongr : xs.map (fm.updateEq (x, y)).lookup = xs.map fm.lookup := by
    apply List.map_congr_left
    intro key hkey
    have hne : key ≠ x := fun he => hx (by simpa [he] using hkey)
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    rw [if_neg hne]
  rw [optMmapEqSome] at hm ⊢
  rw [hcongr]
  exact hm

/-- Canonical standalone-map witness for the exact
    `update_eq_zip_map_flookup` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_updateEqZipMapFlookupExactHOL_f
    {α β : Type} (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Exact port of HOL `pan_commonProps$update_eq_zip_map_flookup`
    (`pan_commonPropsScript.sml:263-272`).  The typed capture gives
    `∀(xs :α list) (f :α |-> β) (n :num) (m :β). n < LENGTH xs ⇒
    FLOOKUP (f |++ ZIP (xs,MAP (λ(x :α). m) xs)) xs❲n❳ = SOME m`.  `f |++` is
    `updateListEq`, `FLOOKUP` is `.lookup`, `EL` is `getElem`, and the map is a
    bare parameter entry.  HOL does not require the key list to be distinct;
    every entry of the zip binds the same value `m`, so the last update at any
    occurring key still yields `some m`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "update_eq_zip_map_flookup"
  (fmap_as_finite_support_parameters := [f])]
theorem updateEqZipMapFlookupExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (f : HolFiniteMapExact α β) (n : Nat) (m : β)
    (hn : n < xs.length) :
    (f.updateListEq (xs.zip (xs.map (fun _ => m)))).lookup (xs[n]'hn) = some m := by
  induction xs generalizing f n with
  | nil => simp at hn
  | cons a xs ih =>
      cases n with
      | zero =>
          simp only [List.getElem_cons_zero, List.map_cons, List.zip_cons_cons,
            HolFiniteMapExact.lookup_updateListEq]
          exact FLOOKUP_FUPDATE_LIST_HOL_of_all_value f.lookup
            ((a, m) :: xs.zip (xs.map (fun _ => m))) m
            (by
              intro entry hentry
              rw [List.mem_cons] at hentry
              rcases hentry with rfl | hentry
              · rfl
              · obtain ⟨_, _, hvalue⟩ :=
                  List.mem_map.mp (List.of_mem_zip hentry).2
                exact hvalue.symm)
            a (by simp)
      | succ k =>
          have hk : k < xs.length := by
            simp only [List.length_cons] at hn
            omega
          simp only [List.getElem_cons_succ, List.map_cons, List.zip_cons_cons,
            HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_cons]
          exact ih (f.updateEq (a, m)) k hk

/-- Canonical standalone-map witness for the exact
    `flookup_fupdate_zip_not_mem` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_flookupFupdateZipNotMemExactHOL_f
    {α β : Type} (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Exact port of HOL `pan_commonProps$flookup_fupdate_zip_not_mem`
    (`pan_commonPropsScript.sml:289-296`).  The typed capture gives
    `∀(xs :α list) (ys :β list) (f :α |-> β) (n :α). LENGTH xs = LENGTH ys ∧
    ¬MEM n xs ⇒ FLOOKUP (f |++ ZIP (xs,ys)) n = FLOOKUP f n`.  `f |++` is
    `updateListEq`, `FLOOKUP` is `.lookup`, and the map is a bare parameter
    entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "flookup_fupdate_zip_not_mem"
  (fmap_as_finite_support_parameters := [f])]
theorem flookupFupdateZipNotMemExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (ys : List β) (f : HolFiniteMapExact α β) (n : α)
    (h : xs.length = ys.length ∧ n ∉ xs) :
    (f.updateListEq (xs.zip ys)).lookup n = f.lookup n := by
  obtain ⟨hlen, hmem⟩ := h
  show FLOOKUP (FUPDATE_LIST_HOL f.lookup (xs.zip ys)) n = FLOOKUP f.lookup n
  rw [FLOOKUP_FUPDATE_LIST_HOL_not_mem]
  rw [List.map_fst_zip (by omega)]
  exact hmem

/-- Canonical standalone-map witness for the exact
    `domsub_commutes_fupdate` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_domsubCommutesFupdateExactHOL_fm
    {α β : Type} (fm : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `pan_commonProps$domsub_commutes_fupdate`
    (`pan_commonPropsScript.sml:319-326`).  The typed capture gives
    `∀(xs :α list) (ys :β list) (fm :α |-> β) (x :α). ¬MEM x xs ∧
    LENGTH xs = LENGTH ys ⇒ (fm |++ ZIP (xs,ys)) \\ x =
    fm \\ x |++ ZIP (xs,ys)`.  `f |++` is `updateListEq`, `\\` is `eraseEq`,
    and the map is a bare parameter entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "domsub_commutes_fupdate"
  (fmap_as_finite_support_parameters := [fm])]
theorem domsubCommutesFupdateExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (ys : List β) (fm : HolFiniteMapExact α β) (x : α)
    (h : x ∉ xs ∧ xs.length = ys.length) :
    (fm.updateListEq (xs.zip ys)).eraseEq x =
      (fm.eraseEq x).updateListEq (xs.zip ys) := by
  obtain ⟨hmem, hlen⟩ := h
  apply HolFiniteMapExact.ext
  funext key
  show FDOMSUB_HOL (FUPDATE_LIST_HOL fm.lookup (xs.zip ys)) x key =
    FUPDATE_LIST_HOL (FDOMSUB_HOL fm.lookup x) (xs.zip ys) key
  have hzip : x ∉ (xs.zip ys).map Prod.fst := by
    rw [List.map_fst_zip (by omega)]
    exact hmem
  rw [FDOMSUB_HOL_FUPDATE_LIST_HOL_commutes (f := fm.lookup) (entries := xs.zip ys)
    (x := x) hzip]

/-- Canonical standalone-map witness for the exact
    `all_distinct_flookup_all_distinct` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_allDistinctFlookupAllDistinctExactHOL_fm
    {α β γ : Type} (fm : HolFiniteMapExact α (β × List γ)) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `pan_commonProps$all_distinct_flookup_all_distinct`
    (`pan_commonPropsScript.sml:510-516`).  The typed capture gives
    `no_overlap (fm :α |-> β # γ list) ∧ FLOOKUP fm (x :α) =
    SOME ((y :β),(zs :γ list)) ⇒ ALL_DISTINCT zs`.  `no_overlap` is the
    reviewed `noOverlapHOL`, `FLOOKUP` is `.lookup`, and the map is a bare
    parameter entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "all_distinct_flookup_all_distinct"
  (fmap_as_finite_support_parameters := [fm])]
theorem allDistinctFlookupAllDistinctExactHOL {α β γ : Type}
    (fm : HolFiniteMapExact α (β × List γ)) (x : α) (y : β) (zs : List γ)
    (h : noOverlapHOL fm ∧ fm.lookup x = some (y, zs)) : zs.Nodup :=
  h.1.1 x y zs h.2

/-- Canonical standalone-map witness for the exact
    `no_overlap_flookup_distinct` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_noOverlapFlookupDistinctExactHOL_fm
    {α β γ : Type} (fm : HolFiniteMapExact α (β × List γ)) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `pan_commonProps$no_overlap_flookup_distinct`
    (`pan_commonPropsScript.sml:520-531`).  The typed capture gives
    `no_overlap (fm :α |-> β # γ list) ∧ (x :α) ≠ (y :α) ∧
    FLOOKUP fm x = SOME ((a :β),(xs :γ list)) ∧
    FLOOKUP fm y = SOME ((b :β),(ys :γ list)) ⇒ distinct_lists xs ys`.
    HOL's Boolean `distinct_lists` is the tagged `distinctListsHol`, `no_overlap`
    is `noOverlapHOL`, and the map is a bare parameter entry. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "no_overlap_flookup_distinct"
  (fmap_as_finite_support_parameters := [fm])]
theorem noOverlapFlookupDistinctExactHOL {α β γ : Type} [DecidableEq γ]
    (fm : HolFiniteMapExact α (β × List γ)) (x y : α) (a b : β) (xs ys : List γ)
    (h : noOverlapHOL fm ∧ x ≠ y ∧ fm.lookup x = some (a, xs) ∧
      fm.lookup y = some (b, ys)) : distinctListsHol xs ys = true := by
  obtain ⟨hno, hxy, hx, hy⟩ := h
  apply (distinctListsHol_eq_true_iff_listDisjoint xs ys).mpr
  intro value hxmem hymem
  exact hxy (hno.2 x y a b xs ys ⟨hx, hy, fun hdisj => hdisj value hxmem hymem⟩)

/-- Exact statement of HOL `pan_commonProps$not_mem_fst_zip_flookup_empty`
    (`pan_commonPropsScript.sml:575-583`), over the canonical carrier but
    deliberately untagged.  The typed capture gives
    `∀(xs :α list) (ys :β list) (x :α). ¬MEM x xs ∧ ALL_DISTINCT xs ∧
    LENGTH xs = LENGTH ys ⇒ FLOOKUP ((FEMPTY :α |-> β) |++ ZIP (xs,ys)) x =
    (NONE :β option)`.  `FEMPTY` is the *constant* `HolFiniteMapExact.empty`,
    not an input binder, and the reviewed `fmap_as_finite_support_parameters`
    qualifier covers only explicitly named `HolFiniteMapExact` parameters, so no
    existing qualifier records this constant-carrier rendering; the theorem
    therefore stays untagged until a qualifier for a constant finite-map
    carrier is reviewed.  `|++` is `updateListEq` and `FLOOKUP` is `.lookup`. -/
theorem notMemFstZipFlookupEmptyExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (ys : List β) (x : α)
    (h : x ∉ xs ∧ xs.Nodup ∧ xs.length = ys.length) :
    ((HolFiniteMapExact.empty : HolFiniteMapExact α β).updateListEq (xs.zip ys)).lookup x =
      none := by
  obtain ⟨hmem, _, hlen⟩ := h
  show FLOOKUP (FUPDATE_LIST_HOL (HolFiniteMapExact.empty : HolFiniteMapExact α β).lookup
    (xs.zip ys)) x = none
  rw [FLOOKUP_FUPDATE_LIST_HOL_not_mem]
  · rfl
  · rw [List.map_fst_zip (by omega)]
    exact hmem

/-- HOL-equality `|++` splits over list concatenation. -/
theorem FUPDATE_LIST_HOL_append [DecidableEq α] (f : FiniteMap α β)
    (l1 l2 : List (α × β)) :
    FUPDATE_LIST_HOL f (l1 ++ l2) = FUPDATE_LIST_HOL (FUPDATE_LIST_HOL f l1) l2 := by
  induction l1 generalizing f with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.cons_append, FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons, ih]

/-- Updating a key with the value it already binds leaves the map unchanged
    (HOL equality). -/
theorem FUPDATE_HOL_eq_self_of_lookup_some [DecidableEq α] (f : FiniteMap α β)
    (x : α) (v : β) (h : FLOOKUP f x = some v) : FUPDATE_HOL f (x, v) = f := by
  funext key
  by_cases hk : key = x
  · subst hk
    simp only [FUPDATE_HOL, if_true]
    exact h.symm
  · simp only [FUPDATE_HOL]
    rw [if_neg hk]

/-- Pointwise congruence of the `|++` fold: maps that agree at one key fold to
    maps that agree at that key. -/
theorem FLOOKUP_FUPDATE_LIST_HOL_congr [DecidableEq α] (f g : FiniteMap α β)
    (entries : List (α × β)) (key : α) (h : FLOOKUP f key = FLOOKUP g key) :
    FLOOKUP (FUPDATE_LIST_HOL f entries) key =
      FLOOKUP (FUPDATE_LIST_HOL g entries) key := by
  induction entries generalizing f g with
  | nil => exact h
  | cons entry rest ih =>
      obtain ⟨k, v⟩ := entry
      rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
      apply ih
      simp only [FLOOKUP_FUPDATE_HOL]
      by_cases hk : key = k
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk]
        exact h

/-- Nested-zip lookup over a list of updates from an arbitrary base map: the
    value at `xs❲n❳` is the pair `(ys❲n❳, zs❲n❳)`. -/
theorem FLOOKUP_FUPDATE_LIST_HOL_zip_zip [DecidableEq α] {β γ : Type}
    (f : FiniteMap α (β × γ)) (xs : List α) (ys : List β) (zs : List γ)
    (hdistinct : xs.Nodup) (hlen1 : xs.length = ys.length)
    (hlen2 : ys.length = zs.length) (n : Nat) (hn : n < xs.length) :
    FLOOKUP (FUPDATE_LIST_HOL f (xs.zip (ys.zip zs))) (xs[n]'hn) =
      some (ys[n]'(by
            rw [← hlen1]
            exact hn),
        zs[n]'(by
            rw [← hlen2]
            rw [← hlen1]
            exact hn)) := by
  induction xs generalizing f ys zs n with
  | nil => simp at hn
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen1
      | cons b ys =>
          cases zs with
          | nil => simp at hlen2
          | cons c zs =>
              rw [List.nodup_cons] at hdistinct
              obtain ⟨ha, hdistinctTail⟩ := hdistinct
              have hlen1' : xs.length = ys.length := by simpa using hlen1
              have hlen2' : ys.length = zs.length := by simpa using hlen2
              cases n with
              | zero =>
                  simp only [List.getElem_cons_zero, List.zip_cons_cons,
                    FUPDATE_LIST_HOL_cons]
                  rw [FLOOKUP_FUPDATE_LIST_HOL_not_mem]
                  · simp
                  · rw [List.map_fst_zip (by
                        rw [List.length_zip]
                        omega)]
                    exact ha
              | succ k =>
                  have hk : k < xs.length := by
                    simp only [List.length_cons] at hn
                    omega
                  simp only [List.getElem_cons_succ, List.zip_cons_cons,
                    FUPDATE_LIST_HOL_cons]
                  exact ih (FUPDATE_HOL f (a, (b, c))) ys zs hdistinctTail hlen1'
                    hlen2' k hk

/-- Canonical standalone-map witness for the exact
    `fm_zip_append_take_drop` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmZipAppendTakeDropExactHOL_f
    {α β : Type} (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Exact port of HOL `pan_commonProps$fm_zip_append_take_drop`
    (`pan_commonPropsScript.sml:595-601`).  The typed capture gives
    `∀(xs :α list) (ys :β list) (zs :β list) (f :α |-> β). ALL_DISTINCT xs ∧
    LENGTH xs = LENGTH (ys ++ zs) ⇒ f |++ ZIP (xs,ys ++ zs) =
    f |++ ZIP (TAKE (LENGTH ys) xs,ys) |++ ZIP (DROP (LENGTH ys) xs,zs)`.
    `f |++` is `updateListEq`, TAKE/DROP are `List.take`/`List.drop`, and the
    map is a bare parameter entry.  HOL's `ALL_DISTINCT xs` is kept as a premise
    although the split identity does not need it. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "fm_zip_append_take_drop"
  (fmap_as_finite_support_parameters := [f])]
theorem fmZipAppendTakeDropExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (ys zs : List β) (f : HolFiniteMapExact α β)
    (h : xs.Nodup ∧ xs.length = (ys ++ zs).length) :
    f.updateListEq (xs.zip (ys ++ zs)) =
      (f.updateListEq ((xs.take ys.length).zip ys)).updateListEq
        ((xs.drop ys.length).zip zs) := by
  obtain ⟨_, hlen⟩ := h
  apply HolFiniteMapExact.ext
  show FUPDATE_LIST_HOL f.lookup (xs.zip (ys ++ zs)) =
    FUPDATE_LIST_HOL (FUPDATE_LIST_HOL f.lookup ((xs.take ys.length).zip ys))
      ((xs.drop ys.length).zip zs)
  have hlenTake : (xs.take ys.length).length = ys.length := by
    rw [List.length_take]
    have hle : ys.length ≤ xs.length := by
      rw [hlen]
      simp
    omega
  rw [← FUPDATE_LIST_HOL_append, ← List.zip_append hlenTake, List.take_append_drop]

/-- Canonical standalone-map witness for the exact
    `fm_update_diff_vars` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmUpdateDiffVarsExactHOL_fm
    {α β : Type} (fm : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `pan_commonProps$fm_update_diff_vars`
    (`pan_commonPropsScript.sml:780-796`).  The typed capture gives
    `(a :α) ≠ (b :α) ⇒ (fm :α |-> β)⟨b ↦ (b'' :β); a ↦ (a' :β);
    b ↦ (b' :β); a ↦ a'⟩ = fm⟨b ↦ b''; a ↦ a'⟩`.  HOL's nested `|+` is the
    chained `updateEq`, and the map is a bare parameter entry.  The binders
    follow the captured free-variable order (`fm_update_diff_vars_vars=`
    `b'',b',a',fm,b,a`). -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "fm_update_diff_vars"
  (fmap_as_finite_support_parameters := [fm])]
theorem fmUpdateDiffVarsExactHOL {α β : Type} [DecidableEq α]
    (b'' : β) (b' : β) (a' : β) (fm : HolFiniteMapExact α β) (b : α) (a : α)
    (h : a ≠ b) :
    (((fm.updateEq (a, a')).updateEq (b, b')).updateEq (a, a')).updateEq (b, b'') =
      (fm.updateEq (a, a')).updateEq (b, b'') := by
  apply HolFiniteMapExact.ext
  show FUPDATE_HOL (FUPDATE_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, a'))
      (b, b')) (a, a')) (b, b'') =
    FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, a')) (b, b'')
  funext key
  by_cases hka : key = a
  · subst hka
    simp [FUPDATE_HOL, h]
  · by_cases hkb : key = b
    · subst hkb
      simp [FUPDATE_HOL]
    · simp [FUPDATE_HOL, hka, hkb]

/-- Exact port of HOL `pan_commonProps$map_some_the_map`
    (`pan_commonPropsScript.sml:615-622`).  The typed capture gives
    `∀(xs :α list) (ys :β list) (f :α -> β option). MAP f xs =
    MAP (SOME :β -> β option) ys ⇒ MAP (λ(n :α). THE (f n)) xs = ys`.  THE is
    the reviewed `holThe`, whose `Nonempty β` instance records that every HOL
    type is inhabited (`total_function_inhabitants`); MAP is `List.map` and
    SOME is `some`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "map_some_the_map"
  (total_function_inhabitants := [β])]
theorem mapSomeTheMapExactHOL {α β : Type} [Nonempty β]
    (xs : List α) (ys : List β) (f : α → Option β)
    (h : xs.map f = ys.map some) : xs.map (fun n => holThe (f n)) = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hx, htail⟩ := h
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨?_, ih ys htail⟩
          rw [hx]
          rfl

/-- Exact statement of HOL `pan_commonProps$fm_empty_zip_flookup_el`
    (`pan_commonPropsScript.sml:479-508`), over the canonical carrier but
    deliberately untagged: HOL's `FEMPTY` is the constant
    `HolFiniteMapExact.empty`, which no reviewed qualifier covers.  The typed
    capture gives `∀(xs :α list) (ys :β list) (zs :γ list) (n :num) (x :α).
    ALL_DISTINCT xs ∧ LENGTH xs = LENGTH ys ∧ LENGTH ys = LENGTH zs ∧
    n < LENGTH xs ∧ xs❲n❳ = x ⇒ FLOOKUP ((FEMPTY :α |-> β # γ) |++
    ZIP (xs,ZIP (ys,zs))) x = SOME (ys❲n❳,zs❲n❳)`.  `|++` is `updateListEq`
    and `FLOOKUP` is `.lookup`; the premise and conclusion `EL` are the reviewed
    total `holEl` (hence `Nonempty α`), as for the other premise-internal EL
    renderings. -/
theorem fmEmptyZipFlookupElExactHOL {α β γ : Type} [DecidableEq α] [Nonempty α]
    [Nonempty β] [Nonempty γ]
    (xs : List α) (ys : List β) (zs : List γ) (n : Nat) (x : α)
    (h : xs.Nodup ∧ xs.length = ys.length ∧ ys.length = zs.length ∧
      n < xs.length ∧ holEl n xs = x) :
    ((HolFiniteMapExact.empty : HolFiniteMapExact α (β × γ)).updateListEq
        (xs.zip (ys.zip zs))).lookup x =
      some (holEl n ys, holEl n zs) := by
  obtain ⟨hd, h1, h2, hn, hx⟩ := h
  show FLOOKUP (FUPDATE_LIST_HOL
    (HolFiniteMapExact.empty : HolFiniteMapExact α (β × γ)).lookup
    (xs.zip (ys.zip zs))) x = some (holEl n ys, holEl n zs)
  rw [holEl_eq_getElem n xs hn] at hx
  rw [← hx]
  rw [holEl_eq_getElem n ys (by
        rw [← h1]
        exact hn),
    holEl_eq_getElem n zs (by
        rw [← h2]
        rw [← h1]
        exact hn)]
  exact FLOOKUP_FUPDATE_LIST_HOL_zip_zip
    (HolFiniteMapExact.empty : HolFiniteMapExact α (β × γ)).lookup xs ys zs hd h1 h2 n hn

/-- Exact statement of HOL `pan_commonProps$fupdate_flookup_zip_elim`
    (`pan_commonPropsScript.sml:546-573`), over the canonical carrier but
    deliberately untagged because both sides use the constant
    `HolFiniteMapExact.empty`, which no reviewed qualifier covers.  The typed
    capture gives `∀(xs :α list) (ys :β list) (zs :α list) (as :β list)
    (x :α). FLOOKUP ((FEMPTY :α |-> β) |++ ZIP (xs,ys)) x = NONE ∧
    LENGTH zs = LENGTH as ∧ LENGTH xs = LENGTH ys ∧ ALL_DISTINCT xs ⇒
    FLOOKUP ((FEMPTY :α |-> β) |++ ZIP (xs,ys) |++ ZIP (zs,as)) x =
    FLOOKUP ((FEMPTY :α |-> β) |++ ZIP (zs,as)) x`.  `|++` is `updateListEq`
    and `FLOOKUP` is `.lookup`. -/
theorem fupdateFlookupZipElimExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (ys : List β) (zs : List α) (as : List β) (x : α)
    (h : ((HolFiniteMapExact.empty : HolFiniteMapExact α β).updateListEq
        (xs.zip ys)).lookup x = none ∧
      zs.length = as.length ∧ xs.length = ys.length ∧ xs.Nodup) :
    (((HolFiniteMapExact.empty : HolFiniteMapExact α β).updateListEq
        (xs.zip ys)).updateListEq (zs.zip as)).lookup x =
      ((HolFiniteMapExact.empty : HolFiniteMapExact α β).updateListEq
        (zs.zip as)).lookup x := by
  obtain ⟨hbase, _, _, _⟩ := h
  have hkey : FLOOKUP (FUPDATE_LIST_HOL
      (HolFiniteMapExact.empty : HolFiniteMapExact α β).lookup (xs.zip ys)) x =
      FLOOKUP (HolFiniteMapExact.empty : HolFiniteMapExact α β).lookup x := by
    simpa [FLOOKUP, HolFiniteMapExact.empty] using hbase
  show FLOOKUP (FUPDATE_LIST_HOL
      (FUPDATE_LIST_HOL (HolFiniteMapExact.empty : HolFiniteMapExact α β).lookup
        (xs.zip ys)) (zs.zip as)) x =
    FLOOKUP (FUPDATE_LIST_HOL (HolFiniteMapExact.empty : HolFiniteMapExact α β).lookup
      (zs.zip as)) x
  rw [FLOOKUP_FUPDATE_LIST_HOL_congr _ _ (zs.zip as) x hkey]

/-- Function-level congruence of the `|++` fold: maps that agree outside the
    updated keys fold to the same map. -/
theorem FUPDATE_LIST_HOL_congr_not_mem [DecidableEq α] (f g : FiniteMap α β)
    (entries : List (α × β))
    (h : ∀ key, key ∉ entries.map Prod.fst → f key = g key) :
    FUPDATE_LIST_HOL f entries = FUPDATE_LIST_HOL g entries := by
  induction entries generalizing f g with
  | nil =>
      funext key
      exact h key (by simp)
  | cons entry rest ih =>
      obtain ⟨k, v⟩ := entry
      rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
      apply ih
      intro key hkey
      show FLOOKUP (FUPDATE_HOL f (k, v)) key = FLOOKUP (FUPDATE_HOL g (k, v)) key
      simp only [FLOOKUP_FUPDATE_HOL]
      by_cases hke : key = k
      · rw [if_pos hke, if_pos hke]
      · rw [if_neg hke, if_neg hke]
        exact h key (by simp [hkey, hke])

/-- Canonical standalone-map witness for the exact `fm_multi_update`
    parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmMultiUpdateExactHOL_fm
    {α β : Type} (fm : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Exact port of HOL `pan_commonProps$fm_multi_update`
    (`pan_commonPropsScript.sml:345-358`).  The typed capture gives
    `∀(xs :α list) (ys :β list) (a :α) (b :β) (c :α) (d :β) (fm :α |-> β).
    ¬MEM a xs ∧ ¬MEM c xs ∧ a ≠ c ∧ LENGTH xs = LENGTH ys ⇒
    fm |++ ((a,b)::(c,d)::ZIP (xs,ys)) |++ ((a,b)::ZIP (xs,ys)) =
    fm |++ ((a,b)::(c,d)::ZIP (xs,ys))`.  `|++` is `updateListEq`, ZIP is
    `List.zip`, and the map is a bare parameter entry.  HOL does not require the
    key list to be distinct, and the Lean proof keeps that generality: the
    second update list repeats only entries the first list already establishes,
    so re-folding it is the identity. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "fm_multi_update"
  (fmap_as_finite_support_parameters := [fm])]
theorem fmMultiUpdateExactHOL {α β : Type} [DecidableEq α]
    (xs : List α) (ys : List β) (a : α) (b : β) (c : α) (d : β)
    (fm : HolFiniteMapExact α β)
    (h : a ∉ xs ∧ c ∉ xs ∧ a ≠ c ∧ xs.length = ys.length) :
    (fm.updateListEq ((a, b) :: (c, d) :: xs.zip ys)).updateListEq
        ((a, b) :: xs.zip ys) =
      fm.updateListEq ((a, b) :: (c, d) :: xs.zip ys) := by
  obtain ⟨ha, hc, hac, hlen⟩ := h
  have hZfst : (xs.zip ys).map Prod.fst = xs := by
    rw [List.map_fst_zip (by omega)]
  have haZ : a ∉ (xs.zip ys).map Prod.fst := by
    rw [hZfst]
    exact ha
  have hcZ : c ∉ (xs.zip ys).map Prod.fst := by
    rw [hZfst]
    exact hc
  have hM0a : FLOOKUP (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d)) a = some b := by
    show FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d) a = some b
    simp [FUPDATE_HOL, hac]
  have hMa : FLOOKUP
      (FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d))
        (xs.zip ys)) a = some b := by
    rw [FLOOKUP_FUPDATE_LIST_HOL_not_mem _ (xs.zip ys) a haZ]
    exact hM0a
  have hMself := FUPDATE_HOL_eq_self_of_lookup_some
    (FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d)) (xs.zip ys))
    a b hMa
  apply HolFiniteMapExact.ext
  show FUPDATE_LIST_HOL (FUPDATE_LIST_HOL fm.lookup ((a, b) :: (c, d) :: xs.zip ys))
      ((a, b) :: xs.zip ys) =
    FUPDATE_LIST_HOL fm.lookup ((a, b) :: (c, d) :: xs.zip ys)
  calc
    FUPDATE_LIST_HOL (FUPDATE_LIST_HOL fm.lookup ((a, b) :: (c, d) :: xs.zip ys))
        ((a, b) :: xs.zip ys)
        = FUPDATE_LIST_HOL fm.lookup
            (((a, b) :: (c, d) :: xs.zip ys) ++ ((a, b) :: xs.zip ys)) :=
          (FUPDATE_LIST_HOL_append fm.lookup _ _).symm
    _ = FUPDATE_LIST_HOL fm.lookup
          ((a, b) :: (c, d) :: (xs.zip ys ++ (a, b) :: xs.zip ys)) := by
          rw [List.cons_append, List.cons_append]
    _ = FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d))
          (xs.zip ys ++ (a, b) :: xs.zip ys) := by
          rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
    _ = FUPDATE_LIST_HOL
          (FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d))
            (xs.zip ys)) ((a, b) :: xs.zip ys) :=
          FUPDATE_LIST_HOL_append _ _ _
    _ = FUPDATE_LIST_HOL
          (FUPDATE_HOL (FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d))
            (xs.zip ys)) (a, b)) (xs.zip ys) := by
          rw [FUPDATE_LIST_HOL_cons]
    _ = FUPDATE_LIST_HOL
          (FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d))
            (xs.zip ys)) (xs.zip ys) := by
          rw [hMself]
    _ = FUPDATE_LIST_HOL (FUPDATE_HOL (FUPDATE_HOL fm.lookup (a, b)) (c, d))
          (xs.zip ys) := by
          apply FUPDATE_LIST_HOL_congr_not_mem
          intro key hkey
          exact FLOOKUP_FUPDATE_LIST_HOL_not_mem _ (xs.zip ys) key hkey
    _ = FUPDATE_LIST_HOL fm.lookup ((a, b) :: (c, d) :: xs.zip ys) := by
          rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]

end Flapjack
