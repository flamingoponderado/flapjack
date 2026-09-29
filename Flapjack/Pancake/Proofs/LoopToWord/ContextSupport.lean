import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.MakeCtxtExact
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

/-!
# Loop-to-word context-domain support

Exact ports of `set_fromNumSet` and `domain_toNumSet` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:278-289`. These support
`make_ctxt` correctness and use the exact Spt and list carriers.
-/

namespace Flapjack.LoopToWord

/-- Local finite-map carrier witness for `WordSemStateFiniteExact` in the
`env_to_list_IMP` theorem below. This records the `fpRegs` and `store`
translations on the full target state; the theorem only observes its
`permute` field. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

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

/-- Exact HOL `env_to_list_IMP` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:410-417`. The result equation
feeds the exact `env_to_list_lookup_equiv` theorem; HOL `fromAList` is rendered
by `sptFromAList`, whose lookup is the same first-match lookup as `ALOOKUP`.
The premise uses the `permute` field of the exact target WordSem state `t`;
`fpRegs` and `store` are recorded by the finite-map carrier qualifier, and
`WordLocW width` by the word-width qualifier. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "env_to_list_IMP"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem envToListIMPHOL {width : Nat} [NeZero width] {C F : Type}
    (env : Spt (WordLocW width)) (target : WordSemStateFiniteExact width C F)
    (entries : List (Nat × WordLocW width)) (permutation : Nat → Nat → Nat)
    (hresult : wordSemEnvToList env target.permute = (entries, permutation)) :
    sptDomain (sptFromAList entries) = sptDomain env ∧
      ∀ key, sptLookup key (sptFromAList entries) = sptLookup key env := by
  obtain ⟨hlookup, _⟩ :=
    wordSemEnvToListLookupEquiv env target.permute entries permutation hresult
  constructor
  · funext key
    simp only [sptDomain]
    rw [sptLookup_sptFromAList, hlookup key]
  · intro key
    rw [sptLookup_sptFromAList, hlookup key]

/-- Exact HOL `cut_env_LN_IMP` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml`: cutting with an empty
second name set returns the first cut as `cut_env`'s union, and exposes that
same pair through `cut_envs`. The only representation qualification is the
indexed Lean `BitVec` model of HOL's polymorphic word values. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_LN_IMP"
  (words_as_type_indexed_bitvec)]
theorem wordSemCutEnvLNIMPHOL {width : Nat} [NeZero width]
    (nameSets : WordLangNumSetHOL) (locals : Spt (WordLocW width))
    (env : Spt (WordLocW width))
    (hcut : wordSemCutEnv (nameSets, (Spt.ln : WordLangNumSetHOL)) locals = some env) :
    wordSemCutEnvs (nameSets, (Spt.ln : WordLangNumSetHOL)) locals =
      some (env, Spt.ln) := by
  have hempty : wordSemCutNames (Spt.ln : WordLangNumSetHOL) locals = some Spt.ln := by
    have hinter : sptInter locals (Spt.ln : WordLangNumSetHOL) = Spt.ln := by
      cases locals <;> simp [sptInter]
    simp [wordSemCutNames, LoopSemStateFiniteExact.sptSubsetLive, hinter]
  unfold wordSemCutEnv at hcut
  cases hfirst : wordSemCutNames nameSets locals with
  | none => simp [wordSemCutEnvs, hfirst, hempty] at hcut
  | some first =>
      have hfirst_eq : first = env := by
        simpa [wordSemCutEnvs, hfirst, hempty, sptUnion] using hcut
      subst env
      simp [wordSemCutEnvs, hfirst, hempty]

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

/-- Exact local HOL `make_ctxt_NOT_MEM`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:317-321`). A name absent
from the input list has the same lookup result before and after exact context
construction. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "make_ctxt_NOT_MEM" 317]
theorem makeCtxtHOL_notMem (names : List Nat) (next : Nat)
    (context : Spt Nat) (key : Nat) (hnot : key ∉ names) :
    sptLookup key (Flapjack.makeCtxtHOL next names context) =
      sptLookup key context := by
  induction names generalizing next context with
  | nil => simp [Flapjack.makeCtxtHOL]
  | cons name names ih =>
      have hnot' : key ≠ name ∧ key ∉ names := by
        simpa only [List.mem_cons, not_or] using hnot
      rcases hnot' with ⟨hne, hnotRest⟩
      calc
        sptLookup key (Flapjack.makeCtxtHOL next (name :: names) context) =
            sptLookup key
              (Flapjack.makeCtxtHOL (next + 2) names
                (sptInsert name next context)) := rfl
        _ = sptLookup key (sptInsert name next context) :=
          ih (next + 2) (sptInsert name next context) hnotRest
        _ = sptLookup key context :=
          sptLookup_sptInsert_ne name key next context hne

/-- Exact HOL `lookup_EL_make_ctxt`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:323-329`). The valid
`List.get` index is HOL's `EL` under the same in-range premise, and `Nodup` is
HOL's `ALL_DISTINCT`; each listed name receives its even register. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_EL_make_ctxt"]
theorem makeCtxtHOL_lookupEL (params : List Nat) (k n : Nat)
    (context : Spt Nat) (hk : k < params.length) (hdistinct : params.Nodup) :
    sptLookup params[k] (Flapjack.makeCtxtHOL n params context) =
      some (2 * k + n) := by
  induction params generalizing k n context with
  | nil => simp at hk
  | cons name rest ih =>
      rcases List.nodup_cons.mp hdistinct with ⟨hname, hrest⟩
      cases k with
      | zero =>
          simp only [List.getElem_cons_zero, Flapjack.makeCtxtHOL]
          rw [makeCtxtHOL_notMem rest (n + 2)
            (sptInsert name n context) name hname]
          rw [sptLookup_sptInsert_same]
          simp
      | succ k =>
          have hk' : k < rest.length := by simp at hk; omega
          change sptLookup rest[k]
              (Flapjack.makeCtxtHOL (n + 2) rest
                (sptInsert name n context)) =
            some (2 * (k + 1) + n)
          calc
            _ = some (2 * k + (n + 2)) :=
              ih k (n + 2) (sptInsert name n context) hk' hrest
            _ = _ := by congr 1 <;> omega

/-- Exact HOL `lookup_make_ctxt_range`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:331-339`). Any register
found after context construction was either already present with the same
value or lies at or above the starting register. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_make_ctxt_range"]
theorem makeCtxtHOL_lookupRange (names : List Nat) (next : Nat)
    (context : Spt Nat) (key value : Nat)
    (hlookup : sptLookup key (Flapjack.makeCtxtHOL next names context) =
      some value) :
    sptLookup key context = some value ∨ next ≤ value := by
  induction names generalizing next context with
  | nil => exact Or.inl hlookup
  | cons name names ih =>
      have hrec := ih (next + 2) (sptInsert name next context) hlookup
      rcases hrec with hsource | hbound
      · by_cases hkey : key = name
        · subst key
          rw [sptLookup_sptInsert_same] at hsource
          have hvalue : value = next := (Option.some.inj hsource).symm
          subst value
          exact Or.inr (by omega)
        · rw [sptLookup_sptInsert_ne name key next context hkey] at hsource
          exact Or.inl hsource
      · exact Or.inr (by omega)

end Flapjack.LoopToWord
