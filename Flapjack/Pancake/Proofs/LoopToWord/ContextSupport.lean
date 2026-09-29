import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.MakeCtxtExact

/-!
# Loop-to-word context-domain support

Exact ports of `set_fromNumSet` and `domain_toNumSet` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:278-289`. These support
`make_ctxt` correctness and use the exact Spt and list carriers.
-/

namespace Flapjack.LoopToWord

/-- Inserting an association-list entry makes its key lookup successfully;
this helper describes the external HOL `fromAList` rendering and has no
CakeML theorem reference of its own. -/
private theorem sptLookup_isSome_sptFromAList_of_mem_fst {α : Type}
    (key : Nat) : ∀ entries : List (Nat × α),
      key ∈ entries.map Prod.fst →
        (sptLookup key (sptFromAList entries)).isSome := by
  intro entries
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      obtain ⟨other, value⟩ := entry
      intro hmem
      change (sptLookup key (sptInsert other value (sptFromAList entries))).isSome
      by_cases hkey : key = other
      · subst key
        rw [sptLookup_sptInsert_same]
        simp
      · have htail : key ∈ entries.map Prod.fst := by
          simpa [List.mem_cons, hkey] using hmem
        rw [sptLookup_sptInsert_ne other key value (sptFromAList entries) hkey]
        exact ih htail

/-- Exact HOL `set_fromNumSet`: the keys enumerated by `fromNumSet` are
precisely the Spt domain. HOL set membership is Lean list membership on the
left and exact `sptMem` (`domain_lookup`) on the right. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "set_fromNumSet"]
theorem fromNumSetHOL_set {α : Type} (tree : Spt α) :
    (fun key => key ∈ fromNumSetHOL tree) = sptDomain tree := by
  ext key
  constructor
  · intro hmem
    have hkeys : key ∈ (sptToAList tree).map Prod.fst := by
      simpa [fromNumSetHOL] using hmem
    have hsome := sptLookup_isSome_sptFromAList_of_mem_fst key
      (sptToAList tree) hkeys
    rw [sptLookup_sptFromAList_sptToAList] at hsome
    exact hsome
  · intro hmem
    change sptMem key tree at hmem
    rw [sptMem_iff_lookup] at hmem
    obtain ⟨value, hlookup⟩ := hmem
    have hfold := sptFoldi_lookup_mem tree 0 [] key value hlookup
    have hpair : (key, value) ∈ sptToAList tree := by
      simpa [sptToAList, sptAcc_eq, lrNext] using hfold
    have hkeys : key ∈ (sptToAList tree).map Prod.fst := by
      exact List.mem_map.mpr ⟨(key, value), hpair, rfl⟩
    simpa [fromNumSetHOL] using hkeys

/-- Exact HOL `domain_toNumSet`: inserting every list member into an empty
Spt gives a domain equal to the list's set, including duplicate names. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "domain_toNumSet"]
theorem sptDomain_toNumSetHOL (names : List Nat) :
    sptDomain (toNumSetHOL names) = (fun key => key ∈ names) := by
  funext key
  apply propext
  induction names with
  | nil => simp [toNumSetHOL, sptDomain]
  | cons name names ih =>
      change sptMem key (sptInsert name () (toNumSetHOL names)) ↔ _
      rw [sptMem_sptInsert]
      change (key = name ∨
        (sptLookup key (toNumSetHOL names)).isSome = true) ↔ _
      simp only [List.mem_cons]
      exact or_congr Iff.rfl (by simpa [sptDomain] using ih)

/-- Exact HOL `domain_make_ctxt`: assigning the listed names into the exact
Spt context adds precisely those names to its domain.  HOL set union is
rendered as disjunction between the old `sptDomain` membership and list
membership. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "domain_make_ctxt"]
theorem sptDomain_makeCtxtHOL (next : Nat) (names : List Nat)
    (context : Spt Nat) :
    sptDomain (Flapjack.makeCtxtHOL next names context) =
      (fun key => sptDomain context key ∨ key ∈ names) := by
  funext key
  apply propext
  induction names generalizing next context with
  | nil => simp [Flapjack.makeCtxtHOL]
  | cons name names ih =>
      change sptDomain
          (Flapjack.makeCtxtHOL (next + 2) names
            (sptInsert name next context)) key ↔ _
      rw [ih]
      change (sptMem key (sptInsert name next context) ∨ key ∈ names) ↔
        (sptMem key context ∨ key ∈ name :: names)
      rw [sptMem_sptInsert]
      simp only [List.mem_cons]
      constructor
      · rintro ((hkey | hctx) | hnames)
        · exact Or.inr (Or.inl hkey)
        · exact Or.inl hctx
        · exact Or.inr (Or.inr hnames)
      · rintro (hctx | hrest)
        · exact Or.inl (Or.inr hctx)
        · rcases hrest with hkey | hnames
          · exact Or.inl (Or.inl hkey)
          · exact Or.inr hnames

/-- Flapjack-specific induction strengthening for `make_ctxt_inj`: adding a
fresh register preserves lookup injectivity while advancing its value bound.
HOL proves this fact inside the `make_ctxt_inj` proof rather than declaring it
as a separate theorem. -/
private theorem sptInsert_preserves_bounded_lookup_injectivity
    (next name : Nat) (context : Spt Nat)
    (hinj : ∀ x y v, sptLookup x context = some v →
      sptLookup y context = some v → x = y ∧ v < next) :
    ∀ x y v, sptLookup x (sptInsert name next context) = some v →
      sptLookup y (sptInsert name next context) = some v →
      x = y ∧ v < next + 2 := by
  have hnext_absent : ∀ key, sptLookup key context ≠ some next := by
    intro key hlookup
    have hbound := (hinj key key next hlookup hlookup).2
    omega
  intro x y v hx hy
  by_cases hxn : x = name
  · subst x
    rw [sptLookup_sptInsert_same] at hx
    have hv : v = next := (Option.some.inj hx).symm
    subst v
    by_cases hyn : y = name
    · exact ⟨hyn.symm, by omega⟩
    · rw [sptLookup_sptInsert_ne name y next context hyn] at hy
      exact False.elim (hnext_absent y hy)
  · rw [sptLookup_sptInsert_ne name x next context hxn] at hx
    by_cases hyn : y = name
    · subst y
      rw [sptLookup_sptInsert_same] at hy
      have hv : v = next := (Option.some.inj hy).symm
      subst v
      exact False.elim (hnext_absent x hx)
    · rw [sptLookup_sptInsert_ne name y next context hyn] at hy
      obtain ⟨hxy, hbound⟩ := hinj x y v hx hy
      exact ⟨hxy, by omega⟩

/-- Exact HOL `make_ctxt_inj`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:296-300`). The incoming
context is injective on equal lookup results whose registers are below
`next`; each `make_ctxt` insertion uses the fresh register `next`, then the
bound advances by two. This is stated over the exact `Spt Nat` carrier and
retains HOL's same-result lookup binders and premise. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "make_ctxt_inj"]
theorem makeCtxtHOL_inj (names : List Nat) (context : Spt Nat) (next : Nat)
    (hinj : ∀ x y v, sptLookup x context = some v →
      sptLookup y context = some v → x = y ∧ v < next) :
    ∀ x y v, sptLookup x (Flapjack.makeCtxtHOL next names context) = some v →
      sptLookup y (Flapjack.makeCtxtHOL next names context) = some v →
      x = y := by
  induction names generalizing context next with
  | nil =>
      intro x y v hx hy
      exact (hinj x y v hx hy).1
  | cons name names ih =>
      intro x y v hx hy
      apply ih (sptInsert name next context) (next + 2)
        (sptInsert_preserves_bounded_lookup_injectivity next name context hinj)
      · exact hx
      · exact hy

/-- Exact local HOL `make_ctxt_APPEND`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:309-315`). Splitting the
input names after `xs` advances the starting register for `ys` by exactly two
per name in the prefix. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "make_ctxt_APPEND" 309]
theorem makeCtxtHOL_append (xs ys : List Nat) (next : Nat)
    (context : Spt Nat) :
    Flapjack.makeCtxtHOL next (xs ++ ys) context =
      Flapjack.makeCtxtHOL (next + 2 * xs.length) ys
        (Flapjack.makeCtxtHOL next xs context) := by
  induction xs generalizing next context with
  | nil => simp [Flapjack.makeCtxtHOL]
  | cons name names ih =>
      simp only [List.cons_append, List.length_cons, Flapjack.makeCtxtHOL]
      rw [ih]
      have hoffset : (next + 2) + 2 * names.length =
          next + 2 * (names.length + 1) := by omega
      rw [hoffset]

end Flapjack.LoopToWord
