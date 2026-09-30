import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.MakeCtxtExact
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

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
same pair through `cut_envs`. The environment payload is arbitrary, as in HOL. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_LN_IMP"]
theorem wordSemCutEnvLNIMPHOL {β : Type}
    (nameSets : WordLangNumSetHOL) (locals : Spt β)
    (env : Spt β)
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

/-- Exact HOL `cut_env_mk_new_cutset_IMP` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:438-444`. A successful
cut by `mk_new_cutset ctxt x1` preserves register zero because that generated
set always contains zero; the second `LN` cut contributes the empty map to the
`cut_env` union. The premise and lookup conclusion use the same exact Spt
`cut_env` definition as HOL; arbitrary environment payloads are retained. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_mk_new_cutset_IMP"]
theorem wordSemCutEnvMkNewCutsetIMPHOL {β : Type}
    (context : Spt Nat) (live : WordLangNumSetHOL)
    (locals result : Spt β)
    (hcut : wordSemCutEnv (mkNewCutsetHOL context live, (Spt.ln : WordLangNumSetHOL))
      locals = some result) :
    sptLookup 0 result = sptLookup 0 locals := by
  have hempty : wordSemCutNames (Spt.ln : WordLangNumSetHOL) locals =
      some (Spt.ln : Spt β) := by
    have hinter : sptInter locals (Spt.ln : WordLangNumSetHOL) = Spt.ln := by
      cases locals <;> simp [sptInter]
    simp [wordSemCutNames, LoopSemStateFiniteExact.sptSubsetLive, hinter]
  unfold wordSemCutEnv at hcut
  cases hfirst : wordSemCutNames (mkNewCutsetHOL context live) locals with
  | none => simp [wordSemCutEnvs, hfirst, hempty] at hcut
  | some first =>
      have hsubset : LoopSemStateFiniteExact.sptSubsetLive
          (mkNewCutsetHOL context live) locals := by
        change (if LoopSemStateFiniteExact.sptSubsetLive
            (mkNewCutsetHOL context live) locals
          then some (sptInter locals (mkNewCutsetHOL context live)) else none) =
          some first at hfirst
        split at hfirst
        · assumption
        · simp at hfirst
      have hfirstEq : sptInter locals (mkNewCutsetHOL context live) = first := by
        simpa [wordSemCutNames, hsubset] using hfirst
      have hzero : sptMem 0 (mkNewCutsetHOL context live) := by
        change (sptLookup 0 (mkNewCutsetHOL context live)).isSome
        simp [mkNewCutsetHOL, sptLookup_sptInsert_same]
      have hcut' : sptUnion (Spt.ln : Spt β) first = result := by
        simpa [wordSemCutEnvs, hfirst, hempty] using hcut
      have hresult : result = first := by
        simpa [sptUnion] using hcut'.symm
      rw [hresult, ← hfirstEq, Flapjack.sptLookup_sptInter]
      change (sptLookup 0 (mkNewCutsetHOL context live)).isSome at hzero
      simp [hzero]

/-- Flapjack-specific proof infrastructure for `cut_env_mk_new_cutset`:
HOL proves this subset fact inline rather than declaring it as a separate
theorem. The context relation maps every live source name to a target register
present in the target locals; the generated cutset also contains register 0. -/
private theorem mkNewCutsetHOL_subsetTarget {width : Nat} [NeZero width]
    (context : Spt Nat) (live : WordLangNumSetHOL)
    (sourceLocals targetLocals : Spt (WordLocW width)) (zeroValue : WordLocW width)
    (hrel : localsRelHOL context sourceLocals targetLocals)
    (hdomain : ∀ name, sptMem name live → sptMem name sourceLocals)
    (hzero : sptLookup 0 targetLocals = some zeroValue) :
    LoopSemStateFiniteExact.sptSubsetLive (mkNewCutsetHOL context live) targetLocals := by
  intro key hmem
  change sptMem key (sptInsert 0 ()
    (toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context)))) at hmem
  rw [sptMem_sptInsert] at hmem
  rcases hmem with hkeyZero | hkeyLive
  · subst key
    exact (sptMem_iff_lookup 0 targetLocals).mpr ⟨zeroValue, hzero⟩
  · have hkeyList : key ∈ (fromNumSetHOL live).map (findVarHOL context) := by
      have hdomainTree := congrFun
        (sptDomain_toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context))) key
      change sptDomain
        (toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context))) key at hkeyLive
      rw [hdomainTree] at hkeyLive
      exact hkeyLive
    obtain ⟨name, hnameList, hfind⟩ := List.mem_map.mp hkeyList
    have hnameLive : sptMem name live := by
      have hdomainNames := congrFun (fromNumSetHOL_set live) name
      change sptDomain live name
      rw [← hdomainNames]
      exact hnameList
    obtain ⟨value, hsource⟩ := (sptMem_iff_lookup name sourceLocals).mp
      (hdomain name hnameLive)
    obtain ⟨register, hcontext, htarget⟩ := hrel.2.2 name value hsource
    have hregisterFind : findVarHOL context name = register := by
      simp [findVarHOL, hcontext]
    have hregisterKey : register = key := hregisterFind.symm.trans hfind
    apply (sptMem_iff_lookup key targetLocals).mpr
    refine ⟨value, ?_⟩
    rw [← hregisterKey]
    exact htarget

/-- Exact HOL `cut_env_mk_new_cutset` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:395-408`. The premise
retains the source locals relation, live-domain subset and target register-zero
lookup; the conclusion keeps the existential cut result and its relation to
the intersection of source locals with the live set. The only representation
qualification is HOL's polymorphic word payload represented by
`WordLocW width` (`BitVec width`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_mk_new_cutset"
  (words_as_type_indexed_bitvec)]
theorem wordSemCutEnvMkNewCutsetHOL {width : Nat} [NeZero width]
    (context : Spt Nat) (live : WordLangNumSetHOL)
    (sourceLocals targetLocals : Spt (WordLocW width)) (zeroValue : WordLocW width)
    (hpremises : localsRelHOL context sourceLocals targetLocals ∧
      (∀ name, sptMem name live → sptMem name sourceLocals) ∧
      sptLookup 0 targetLocals = some zeroValue) :
    ∃ result,
      wordSemCutEnv (mkNewCutsetHOL context live, (Spt.ln : WordLangNumSetHOL))
        targetLocals = some result ∧
      localsRelHOL context (sptInter sourceLocals live) result := by
  rcases hpremises with ⟨hrel, hdomain, hzero⟩
  have hsubset := mkNewCutsetHOL_subsetTarget context live sourceLocals
    targetLocals zeroValue hrel hdomain hzero
  have hempty : wordSemCutNames (Spt.ln : WordLangNumSetHOL) targetLocals =
      some (Spt.ln : Spt (WordLocW width)) := by
    have hinter : sptInter targetLocals (Spt.ln : WordLangNumSetHOL) = Spt.ln := by
      cases targetLocals <;> simp [sptInter]
    simp [wordSemCutNames, LoopSemStateFiniteExact.sptSubsetLive, hinter]
  refine ⟨sptInter targetLocals (mkNewCutsetHOL context live), ?_, ?_⟩
  · simp only [wordSemCutEnv, wordSemCutEnvs]
    rw [hempty]
    simp only [wordSemCutNames, if_pos hsubset, sptUnion]
  · rcases hrel with ⟨hinjective, heven, hlookups⟩
    refine ⟨hinjective, heven, ?_⟩
    intro name value hsourceCut
    rw [Flapjack.sptLookup_sptInter] at hsourceCut
    by_cases hlive : (sptLookup name live).isSome
    · have hsource : sptLookup name sourceLocals = some value := by
        simpa [hlive] using hsourceCut
      obtain ⟨register, hcontext, htarget⟩ := hlookups name value hsource
      have hnameLive : sptMem name live := by
        change (sptLookup name live).isSome
        exact hlive
      have hnameList : name ∈ fromNumSetHOL live := by
        have hdomainNames := congrFun (fromNumSetHOL_set live) name
        change sptDomain live name at hnameLive
        rw [← hdomainNames] at hnameLive
        exact hnameLive
      have hregisterFind : findVarHOL context name = register := by
        simp [findVarHOL, hcontext]
      have hregisterTree : sptMem register
          (toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context))) := by
        have hregisterList : register ∈
            (fromNumSetHOL live).map (findVarHOL context) :=
          List.mem_map.mpr ⟨name, hnameList, hregisterFind⟩
        have hdomainTree := congrFun
          (sptDomain_toNumSetHOL
            ((fromNumSetHOL live).map (findVarHOL context))) register
        change sptDomain
          (toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context))) register
        rw [hdomainTree]
        exact hregisterList
      have hregisterCut : sptMem register (mkNewCutsetHOL context live) := by
        change sptMem register (sptInsert 0 ()
          (toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context))))
        rw [sptMem_sptInsert]
        exact Or.inr hregisterTree
      have htargetCut : sptLookup register
          (sptInter targetLocals (mkNewCutsetHOL context live)) = some value := by
        rw [Flapjack.sptLookup_sptInter]
        change (sptLookup register (mkNewCutsetHOL context live)).isSome at hregisterCut
        simp [hregisterCut, htarget]
      exact ⟨register, hcontext, htargetCut⟩
    · simp [hlive] at hsourceCut

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

/-- Exact HOL `lookup_make_ctxt_EVEN`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:341-353`). Existing
context lookups remain even, and `make_ctxt` inserts only the even register
sequence beginning at its even start. HOL `EVEN v` is represented by the exact
Lean arithmetic predicate `v % 2 = 0`, as in the existing `find_var` ports. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_make_ctxt_EVEN"]
theorem makeCtxtHOL_lookupEven (names : List Nat) (start : Nat)
    (context : Spt Nat) (key value : Nat)
    (hstart : start % 2 = 0)
    (hcontext : ∀ k v, sptLookup k context = some v → v % 2 = 0)
    (hlookup : sptLookup key (Flapjack.makeCtxtHOL start names context) =
      some value) :
    value % 2 = 0 := by
  induction names generalizing start context with
  | nil => exact hcontext key value (by simpa [Flapjack.makeCtxtHOL] using hlookup)
  | cons name names ih =>
      have hstart' : (start + 2) % 2 = 0 := by omega
      have hcontext' :
          ∀ k v, sptLookup k (sptInsert name start context) = some v → v % 2 = 0 := by
        intro k v hlookup'
        by_cases hkey : k = name
        · subst k
          rw [sptLookup_sptInsert_same] at hlookup'
          have hv : v = start := Option.some.inj hlookup'.symm
          subst v
          exact hstart
        · rw [sptLookup_sptInsert_ne name k start context hkey] at hlookup'
          exact hcontext k v hlookup'
      apply ih (start + 2) (sptInsert name start context) hstart' hcontext'
      exact hlookup

/-- Auxiliary recursive form of the exact external HOL `fromList2` fold.
This helper is Flapjack proof infrastructure; the tagged source definition is
`Flapjack.sptFromList2`. -/
private def sptFromList2At {α : Type} (next : Nat) (values : List α)
    (context : Spt α) : Spt α :=
  match values with
  | [] => context
  | value :: rest => sptFromList2At (next + 2) rest (sptInsert next value context)

private theorem sptFromList2At_eq_foldl {α : Type} (next : Nat)
    (values : List α) (context : Spt α) :
    sptFromList2At next values context =
      (values.foldl (fun (acc : Nat × Spt α) value =>
        (acc.1 + 2, sptInsert acc.1 value acc.2)) (next, context)).2 := by
  induction values generalizing next context with
  | nil => rfl
  | cons value values ih =>
      simp only [sptFromList2At, List.foldl_cons]
      exact ih (next + 2) (sptInsert next value context)

/-- Later `fromList2` entries have larger keys and preserve every lookup below
the next insertion key. -/
private theorem sptLookup_sptFromList2At_below {α : Type} (key next : Nat)
    (values : List α) (context : Spt α) (hkey : key < next) :
    sptLookup key (sptFromList2At next values context) = sptLookup key context := by
  induction values generalizing next context with
  | nil => rfl
  | cons value values ih =>
      change sptLookup key
        (sptFromList2At (next + 2) values (sptInsert next value context)) =
        sptLookup key context
      rw [ih (next + 2) (sptInsert next value context) (by omega)]
      exact sptLookup_sptInsert_ne next key value context (by omega)

/-- A valid index in the local sequence maps to its even `fromList2` key. -/
private theorem sptLookup_sptFromList2At_get {α : Type} (next : Nat)
    (values : List α) (context : Spt α) (index : Nat)
    (hindex : index < values.length) :
    sptLookup (next + 2 * index) (sptFromList2At next values context) =
      some values[index] := by
  induction values generalizing next context index with
  | nil => simp at hindex
  | cons value values ih =>
      cases index with
      | zero =>
          change sptLookup next
            (sptFromList2At (next + 2) values (sptInsert next value context)) =
            some value
          rw [sptLookup_sptFromList2At_below next (next + 2) values
            (sptInsert next value context) (by omega)]
          exact sptLookup_sptInsert_same next value context
      | succ index =>
          have hindex' : index < values.length := by simp at hindex; omega
          change sptLookup (next + 2 * (index + 1))
            (sptFromList2At (next + 2) values (sptInsert next value context)) =
            some values[index]
          have hkey : next + 2 * (index + 1) = (next + 2) + 2 * index := by omega
          rw [hkey]
          exact ih (next + 2) (sptInsert next value context) index hindex'

/-- Unqualified support for exact HOL `misc$fromList2_def`: an in-range
sequence element is found at twice its zero-based index. -/
theorem sptLookup_sptFromList2_get {α : Type} (values : List α)
    (index : Nat) (hindex : index < values.length) :
    sptLookup (2 * index) (sptFromList2 values) = some values[index] := by
  change sptLookup (2 * index)
    (values.foldl (fun (acc : Nat × Spt α) value =>
      (acc.1 + 2, sptInsert acc.1 value acc.2)) (0, .ln)).2 = _
  rw [← sptFromList2At_eq_foldl]
  simpa using sptLookup_sptFromList2At_get 0 values .ln index hindex

/-- Exact HOL `locals_rel_make_ctxt` (`cakeml/pancake/proofs/loop_to_wordProofScript.sml:356-384`).
The context, local maps, and `make_ctxt` use exact `Spt` carriers; source
`fromAList (ZIP ...)` is represented by `sptFromAList`, and result locals by
the exact external `fromList2` port `sptFromList2`. `ALL_DISTINCT` is
`List.Nodup`, `DISJOINT (set params) (set xs)` is the stated membership
implication, and `EVEN` is `% 2 = 0`. The sole representation qualifier is
HOL words to the width-indexed `WordLocW` translation. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_make_ctxt"
  (words_as_type_indexed_bitvec)]
theorem localsRelHOLMakeCtxt {width : Nat} [NeZero width]
    (params xs : List Nat) (values : List (WordLocW width))
    (retv : WordLocW width)
    (hpremises : params.Nodup ∧
      (∀ name, name ∈ params → name ∉ xs) ∧ params.length = values.length) :
    localsRelHOL (Flapjack.makeCtxtHOL 2 (params ++ xs) (.ln : Spt Nat))
      (sptFromAList (params.zip values)) (sptFromList2 (retv :: values)) := by
  rcases hpremises with ⟨hdistinct, hdisjoint, hlength⟩
  refine ⟨?_, ?_, ?_⟩
  · intro left right hleft hright hfind
    obtain ⟨leftValue, hleftLookup⟩ := (sptMem_iff_lookup left
      (Flapjack.makeCtxtHOL 2 (params ++ xs) (.ln : Spt Nat))).mp hleft
    obtain ⟨rightValue, hrightLookup⟩ := (sptMem_iff_lookup right
      (Flapjack.makeCtxtHOL 2 (params ++ xs) (.ln : Spt Nat))).mp hright
    have hequal : leftValue = rightValue := by
      simp [findVarHOL, hleftLookup, hrightLookup] at hfind
      exact hfind
    have hbase : ∀ x y v, sptLookup x (.ln : Spt Nat) = some v →
        sptLookup y (.ln : Spt Nat) = some v → x = y ∧ v < 2 := by
      intro x y v hx _
      simp at hx
    have hinj := makeCtxtHOL_inj (params ++ xs) (.ln : Spt Nat) 2 hbase
    exact hinj left right leftValue hleftLookup (by simpa [hequal] using hrightLookup)
  · intro name register hlookup
    have heven := makeCtxtHOL_lookupEven (params ++ xs) 2 (.ln : Spt Nat)
      name register (by decide) (by intro key value h; simp at h) hlookup
    have hrange := makeCtxtHOL_lookupRange (params ++ xs) 2 (.ln : Spt Nat)
      name register hlookup
    rcases hrange with hnone | hbound
    · simp at hnone
    · exact ⟨by omega, heven⟩
  · intro name value hsource
    rw [sptLookup_sptFromAList] at hsource
    have hpair := sptAListLookup_mem name (params.zip values) value hsource
    obtain ⟨index, hindexParams, hindexValues, hname, hvalue⟩ :=
      mem_zip_getElem params values (name, value) hpair
    have hname' : params[index]'hindexParams = name := by simpa using hname
    have hvalue' : values[index]'hindexValues = value := by simpa using hvalue
    have hparamMem : params[index]'hindexParams ∈ params := List.getElem_mem _
    have hnotXs : name ∉ xs := by simpa [hname'] using hdisjoint _ hparamMem
    have hcontext : sptLookup name
        (Flapjack.makeCtxtHOL 2 (params ++ xs) (.ln : Spt Nat)) =
        some (2 * index + 2) := by
      rw [makeCtxtHOL_append params xs 2 (.ln : Spt Nat)]
      rw [makeCtxtHOL_notMem xs (2 + 2 * params.length)
        (Flapjack.makeCtxtHOL 2 params (.ln : Spt Nat)) name hnotXs]
      rw [← hname']
      have hlookup := makeCtxtHOL_lookupEL params index 2 (.ln : Spt Nat)
        hindexParams hdistinct
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlookup
    refine ⟨2 * index + 2, hcontext, ?_⟩
    have htargetBound : index + 1 < (retv :: values).length := by
      simp only [List.length_cons]
      omega
    have htarget : sptLookup (2 * (index + 1)) (sptFromList2 (retv :: values)) =
        some (retv :: values)[index + 1] :=
      sptLookup_sptFromList2_get (retv :: values) (index + 1) htargetBound
    have htarget' : sptLookup (2 * index + 2) (sptFromList2 (retv :: values)) =
        some values[index] := by
      simpa [hvalue', Nat.mul_add] using htarget
    simpa [hvalue, Nat.mul_add] using htarget'

/-- Exact HOL `locals_rel_mk_ctxt_ln`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1505-1525`). A positive
even initial register keeps every `make_ctxt` assignment positive and even;
the input local tree is empty, so its lookup-simulation clause is vacuous.
The sole representation qualifier is HOL words to width-indexed `WordLocW`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_mk_ctxt_ln"
  (words_as_type_indexed_bitvec)]
theorem localsRelHOLMkCtxtLn {width : Nat} [NeZero width]
    (next : Nat) (names : List Nat) (targetLocals : Spt (WordLocW width))
    (hpremises : 0 < next ∧ next % 2 = 0) :
    localsRelHOL (Flapjack.makeCtxtHOL next names (.ln : Spt Nat))
      (.ln : Spt (WordLocW width)) targetLocals := by
  rcases hpremises with ⟨hpositive, hevenStart⟩
  refine ⟨?_, ?_, ?_⟩
  · intro left right hleft hright hfind
    obtain ⟨leftValue, hleftLookup⟩ := (sptMem_iff_lookup left
      (Flapjack.makeCtxtHOL next names (.ln : Spt Nat))).mp hleft
    obtain ⟨rightValue, hrightLookup⟩ := (sptMem_iff_lookup right
      (Flapjack.makeCtxtHOL next names (.ln : Spt Nat))).mp hright
    have hequal : leftValue = rightValue := by
      simp [findVarHOL, hleftLookup, hrightLookup] at hfind
      exact hfind
    have hbase : ∀ x y v, sptLookup x (.ln : Spt Nat) = some v →
        sptLookup y (.ln : Spt Nat) = some v → x = y ∧ v < next := by
      intro x y v hx _
      simp at hx
    have hinj := makeCtxtHOL_inj names (.ln : Spt Nat) next hbase
    exact hinj left right leftValue hleftLookup (by simpa [hequal] using hrightLookup)
  · intro name register hlookup
    have heven := makeCtxtHOL_lookupEven names next (.ln : Spt Nat)
      name register hevenStart (by intro key value h; simp at h) hlookup
    have hrange := makeCtxtHOL_lookupRange names next (.ln : Spt Nat)
      name register hlookup
    rcases hrange with hnone | hbound
    · simp at hnone
    · exact ⟨by omega, heven⟩
  · intro name value hsource
    simp at hsource

end Flapjack.LoopToWord
