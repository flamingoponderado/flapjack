import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact update support for the Loop-to-Word locals relation

Ports the two update lemmas immediately following `locals_rel_def` in
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:195-220`.  Both use the
same exact Spt and `WordLocW` carriers reviewed with `localsRelHOL`.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `locals_rel_insert`: inserting one mapped source local and its
word into the corresponding target register preserves the locals relation. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_insert"
  (words_as_type_indexed_bitvec)]
theorem localsRelHOLInsert {width : Nat} [NeZero width]
    (context : Spt Nat) (sourceLocals targetLocals : Spt (WordLocW width))
    (name : Nat) (value : WordLocW width)
    (hpremises : localsRelHOL context sourceLocals targetLocals ∧
      sptMem name context) :
    localsRelHOL context (sptInsert name value sourceLocals)
      (sptInsert (findVarHOL context name) value targetLocals) := by
  rcases hpremises with ⟨hrel, hname⟩
  rcases hrel with ⟨hinjective, heven, hsim⟩
  refine ⟨hinjective, heven, ?_⟩
  intro key current hlookup
  by_cases hkey : key = name
  · subst key
    rw [sptLookup_sptInsert_same] at hlookup
    injection hlookup with hcurrent
    subst current
    obtain ⟨register, hcontext⟩ := (sptMem_iff_lookup name context).mp hname
    have hfind : findVarHOL context name = register := by
      simp [findVarHOL, hcontext]
    refine ⟨register, hcontext, ?_⟩
    rw [hfind]
    exact sptLookup_sptInsert_same register value targetLocals
  · rw [sptLookup_sptInsert_ne name key value sourceLocals hkey] at hlookup
    obtain ⟨register, hcontext, htarget⟩ := hsim key current hlookup
    have hkeyMem : sptMem key context :=
      (sptMem_iff_lookup key context).2 ⟨register, hcontext⟩
    obtain ⟨nameRegister, hnameContext⟩ :=
      (sptMem_iff_lookup name context).mp hname
    have hregisterFind : findVarHOL context key = register := by
      simp [findVarHOL, hcontext]
    have hnameFind : findVarHOL context name = nameRegister := by
      simp [findVarHOL, hnameContext]
    have hregisterNe : register ≠ findVarHOL context name := by
      intro heq
      apply hkey
      have hregisterEq : register = nameRegister := by
        calc
          register = findVarHOL context name := heq
          _ = nameRegister := hnameFind
      have hfindEq : findVarHOL context key = findVarHOL context name := by
        rw [hregisterFind, hnameFind]
        exact hregisterEq
      apply hinjective key name hkeyMem hname
      exact hfindEq
    refine ⟨register, hcontext, ?_⟩
    rw [sptLookup_sptInsert_ne (findVarHOL context name) register value
      targetLocals hregisterNe]
    exact htarget

/-- Exact HOL `locals_rel_insert_unmapped`: adding a target local at a register
not selected by any context name preserves the locals relation. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml"
  "locals_rel_insert_unmapped" (words_as_type_indexed_bitvec)]
theorem localsRelHOLInsertUnmapped {width : Nat} [NeZero width]
    (context : Spt Nat) (sourceLocals targetLocals : Spt (WordLocW width))
    (register : Nat) (value : WordLocW width)
    (hpremises : localsRelHOL context sourceLocals targetLocals ∧
      (∀ name, sptMem name context → findVarHOL context name ≠ register)) :
    localsRelHOL context sourceLocals (sptInsert register value targetLocals) := by
  rcases hpremises with ⟨hrel, hunmapped⟩
  rcases hrel with ⟨hinjective, heven, hsim⟩
  refine ⟨hinjective, heven, ?_⟩
  intro name current hsource
  obtain ⟨mapped, hcontext, htarget⟩ := hsim name current hsource
  have hmem : sptMem name context :=
    (sptMem_iff_lookup name context).2 ⟨mapped, hcontext⟩
  have hfind : findVarHOL context name = mapped := by
    simp [findVarHOL, hcontext]
  have hmappedNe : mapped ≠ register := by
    intro heq
    exact (hunmapped name hmem) (by rw [hfind, heq])
  refine ⟨mapped, hcontext, ?_⟩
  rw [sptLookup_sptInsert_ne register mapped value targetLocals hmappedNe]
  exact htarget

/-- Exact HOL `locals_rel_alist_insert`: parallel source/target list updates
preserve the local relation when every updated source name is in the context.
HOL list membership is represented directly by `List.mem`; `alist_insert` is
the reviewed `sptAlistInsert` rendering. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml"
  "locals_rel_alist_insert" (words_as_type_indexed_bitvec)]
theorem localsRelHOLAlistInsert {width : Nat} [NeZero width]
    (context : Spt Nat) :
    ∀ (names : List Nat) (values : List (WordLocW width))
      (sourceLocals targetLocals : Spt (WordLocW width)),
      (localsRelHOL context sourceLocals targetLocals ∧
        ∀ name, name ∈ names → sptMem name context) →
      localsRelHOL context
        (LoopSemStateFiniteExact.sptAlistInsert names values sourceLocals)
        (LoopSemStateFiniteExact.sptAlistInsert
          (names.map (findVarHOL context)) values targetLocals) := by
  intro names
  induction names with
  | nil =>
      intro values sourceLocals targetLocals hpremises
      simpa [LoopSemStateFiniteExact.sptAlistInsert] using hpremises.1
  | cons name names ih =>
      intro values sourceLocals targetLocals hpremises
      cases values with
      | nil =>
          simpa [LoopSemStateFiniteExact.sptAlistInsert] using hpremises.1
      | cons value values =>
          simp only [LoopSemStateFiniteExact.sptAlistInsert, List.map_cons]
          apply localsRelHOLInsert
          constructor
          · apply ih
            constructor
            · exact hpremises.1
            · intro tailName htail
              exact hpremises.2 tailName (List.mem_cons_of_mem name htail)
          · exact hpremises.2 name (by simp)

end Flapjack.LoopToWord
