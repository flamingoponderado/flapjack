module

public import Flapjack.Pancake.Semantics.PanCommonProps
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

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

end Flapjack
