import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-!
# crep_to_loop `code_rel2_def` and `mk_ctxt_code_imp_code_rel2`

Exact ports of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`code_rel2_def` (3842) and `mk_ctxt_code_imp_code_rel2` (3861) over the exact
carriers (bead `flapjack-pxn.18.5.6.33.22`). `FMAP_MAP2` is
`HolFiniteMapExact.map2`, `crep_arith$simp_prog` the tagged `crepSimpProgHOL`,
`code_rel` the tagged exact `crepToLoopCodeRelExact`, `mk_ctxt` the tagged
`mkCtxtExact`, `compile_prog` the tagged `compileProgHOLExact`, and
`fromAList` the exact `sptFromAList` rendering. `alist_to_fmap` is represented
by the local `alistToFmapCodeExact` adapter because its source is the external
HOL `alistTheory`; the adapter preserves `FOLDR FUPDATE FEMPTY` first-key-wins
behavior using HOL key equality.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

/-! Same-module relation witness for `code_rel2_def`'s
`CrepToLoopContextExact` carrier; the standalone `s_code` parameter is
validated at its `HolFiniteMapExact` binder. -/
namespace CrepToLoopCodeRel2Witnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCodeRel2Witnesses

/-- Exact HOL `code_rel2_def` (`crep_to_loopProofScript.sml:3842-3845`):
    `code_rel2 ctxt s_code t_code <=
      code_rel ctxt (FMAP_MAP2 (\(s,n,p). (n,crep_arith$simp_prog p)) s_code) t_code`.
    The finite-support qualifier records the owning context's `funcs` field and
    the `s_code` binder; `HolFiniteMapExact.map2` preserves the source finite
    map's support and maps each present value exactly once. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel2_def"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.funcs, s_code])
  (words_as_type_indexed_bitvec)]
def crepToLoopCodeRel2Exact {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width)) : Prop :=
  crepToLoopCodeRelExact ctxt
    (s_code.map2 (fun entry =>
      match entry with
      | (_, parameters, program) => (parameters, crepSimpProgHOL program)))
    t_code

/-- Flapjack-specific representation of HOL `alist_to_fmap` from the external
`alistTheory`: reverse followed by left-to-right updates matches `FOLDR
FUPDATE FEMPTY`, so the first occurrence of a duplicate key wins. The map uses
HOL equality through the exact finite-support update constructor. -/
def alistToFmapCodeExact {width : Nat} [NeZero width]
    (entries : List (MlString × List Nat × CrepProgHOL width)) :
    HolFiniteMapExact MlString (List Nat × CrepProgHOL width) :=
  HolFiniteMapExact.updateList HolFiniteMapExact.empty entries.reverse

private theorem fupdateListHOL_eq {α β : Type} [DecidableEq α] [BEq α]
    [LawfulBEq α] (f : FiniteMap α β) (entries : List (α × β)) :
    FUPDATE_LIST_HOL f entries = FUPDATE_LIST f entries :=
  FUPDATE_LIST_HOL_eq_FUPDATE_LIST f entries

theorem flookup_fupdateList_reverse_of_mem
    {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (entries : List (α × β)) (key : α) (value : β),
      (entries.map Prod.fst).Nodup → (key, value) ∈ entries →
      FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) key = some value
  | [], _, _, _, h => by simp at h
  | entry :: entries, key, value, hnodup, hmem => by
      simp only [List.reverse_cons, FUPDATE_LIST, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      simp only [FLOOKUP, FUPDATE]
      rw [List.map_cons] at hnodup
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp only [beq_self_eq_true, if_true]
      · have hneq : entry.1 ≠ key := by
          intro heq
          apply hparts.1
          rw [heq]
          exact List.mem_map_of_mem htail
        have hbeq : (entry.1 == key) = false := by
          cases hvalue : (entry.1 == key) with
          | false => rfl
          | true => exact False.elim (hneq (beq_iff_eq.mp hvalue))
        simp only [hbeq, Bool.false_eq_true, if_false]
        exact flookup_fupdateList_reverse_of_mem entries key value hparts.2 htail

theorem flookup_fupdateList_reverse_mem'
    {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (entries : List (α × β)) (key : α) (value : β),
      FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) key = some value →
      (key, value) ∈ entries
  | [], key, value, h => by simp [FUPDATE_LIST, FLOOKUP, FEMPTY] at h
  | entry :: entries, key, value, h => by
      simp only [List.reverse_cons, FUPDATE_LIST, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at h
      simp only [FLOOKUP, FUPDATE] at h
      split at h
      · rename_i hkey
        cases h
        have heq : entry.1 = key := LawfulBEq.eq_of_beq hkey
        subst key
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (flookup_fupdateList_reverse_mem' entries key value h)

private theorem holFiniteMapExact_ext {α β : Type}
    {left right : HolFiniteMapExact α β} (h : left.lookup = right.lookup) :
    left = right := by
  cases left
  cases right
  simp only at h
  subst h
  rfl

private theorem foldr_max_range (length : Nat) :
    (List.range length).foldr max 0 = length - 1 := by
  have hfold : ∀ start, (List.range length).foldr max start =
      if length = 0 then start else max start (length - 1) := by
    induction length with
    | zero => intro start; simp
    | succ length ih =>
        intro start
        rw [List.range_succ, List.foldr_append]
        simp only [List.foldr_cons, List.foldr_nil]
        rw [ih]
        split <;> simp_all <;> omega
  rw [hfold]
  split <;> omega

private theorem compFuncContextEqCtxtFcExact {width : Nat} [NeZero width]
    (target : AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width))
    (parameters : List Nat) :
    mkCtxtExact target (makeVmapExact parameters)
        (crepToLoopMakeFuncsExactExecutable programs)
        (parameters.length - 1) =
      ctxtFcExact target (crepToLoopMakeFuncsExactHOL programs)
        parameters (List.range parameters.length) := by
  simp only [mkCtxtExact, ctxtFcExact, CrepToLoopContextExact.mk.injEq]
  refine ⟨?_, ?_, ?_, trivial⟩
  · apply holFiniteMapExact_ext
    funext key
    simp only [makeVmapExact, HolFiniteMapExact.lookup_updateListEq,
      HolFiniteMapExact.lookup_updateList, fupdateListHOL_eq]
  · apply holFiniteMapExact_ext
    funext key
    exact crepToLoopMakeFuncsExactExecutable_lookup_eq_HOL programs key
  · simp [foldr_max_range]

/-- Exact HOL `mk_ctxt_code_imp_code_rel2`
(`crep_to_loopProofScript.sml:3861-3886`). It preserves `c`, `crep_code`,
`start`, and `np`, both source premises, and the conclusion through the exact
`mk_ctxt`, `make_funcs`, `compile_prog`, `code_rel2`, and Spt carriers. The
standalone maps occur only as values of those definitions, so only the reviewed
word-width qualifier is applicable. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mk_ctxt_code_imp_code_rel2"
  (words_as_type_indexed_bitvec)]
theorem mkCtxtCodeImpCodeRel2Exact {width : Nat} [NeZero width] :
    ∀ (target : AsmArchitecture)
      (programs : List (MlString × List Nat × CrepProgHOL width))
      (start : MlString) (program : CrepProgHOL width),
      (programs.map Prod.fst).Nodup ∧ holAlookup programs start = some ([], program) →
      crepToLoopCodeRel2Exact
        (mkCtxtExact target HolFiniteMapExact.empty
          (crepToLoopMakeFuncsExactHOL programs) 0)
        (alistToFmapCodeExact programs)
        (sptFromAList (compileProgHOLExact target programs)) := by
  intro target programs start program ⟨hnodup, _hstart⟩
  refine ⟨?_, ?_⟩
  · change crepToLoopDistinctFuncs
      (crepToLoopMakeFuncsExactHOL programs).lookup
    have hdistinct := distinct_make_funcs programs
    intro x y n m rm rm' hx hy hnm
    apply hdistinct x y n m rm rm'
    · simpa only [FLOOKUP] using hx
    · simpa only [FLOOKUP] using hy
    · exact hnm
  · intro function parameters body hcompiled
    simp only [HolFiniteMapExact.lookup_map2] at hcompiled
    cases hsource : (alistToFmapCodeExact programs).lookup function with
    | none => simp [hsource] at hcompiled
    | some value =>
        obtain ⟨sourceParameters, sourceProgram⟩ := value
        simp only [hsource, Option.map_some, Option.some.injEq, Prod.mk.injEq]
          at hcompiled
        obtain ⟨rfl, rfl⟩ := hcompiled
        have hmem : (function, sourceParameters, sourceProgram) ∈ programs := by
          rw [alistToFmapCodeExact, HolFiniteMapExact.lookup_updateList] at hsource
          exact flookup_fupdateList_reverse_mem' programs function
            (sourceParameters, sourceProgram) hsource
        obtain ⟨index, hindex, hsourceEntry⟩ := List.mem_iff_getElem.mp hmem
        have hmakeEntry :
            (function, (firstLoopName + index, sourceParameters.length)) ∈
              (programs.zip (List.range programs.length)).map
                (fun entry => (entry.1.1,
                  (firstLoopName + entry.2, entry.1.2.1.length))) := by
          apply List.mem_map.mpr
          have hbound : index < (programs.zip (List.range programs.length)).length := by
            simp [hindex]
          have hzipmem := List.getElem_mem hbound
          have hzipmem' : (programs[index]'hindex, index) ∈
              programs.zip (List.range programs.length) := by
            simpa only [List.getElem_zip, List.getElem_range] using hzipmem
          exact ⟨(programs[index]'hindex, index), hzipmem', by
            simp [hsourceEntry]⟩
        have hentries :
            (((programs.zip (List.range programs.length)).map
                (fun entry => (entry.1.1,
                  (firstLoopName + entry.2, entry.1.2.1.length)))).map Prod.fst).Nodup := by
          have hmapFst :
              (((programs.zip (List.range programs.length)).map
                  (fun entry => (entry.1.1,
                    (firstLoopName + entry.2, entry.1.2.1.length)))).map Prod.fst) =
                programs.map Prod.fst := by
            rw [List.map_map]
            change List.map (Prod.fst ∘ Prod.fst) _ = _
            rw [← List.map_map, List.map_fst_zip (by simp)]
          rw [hmapFst]
          exact hnodup
        have hmake :
            (crepToLoopMakeFuncsExactHOL programs).lookup function =
              some (firstLoopName + index, sourceParameters.length) := by
          letI : BEq MlString := (inferInstance : BEq MlString)
          letI : LawfulBEq MlString := inferInstance
          letI : DecidableEq MlString :=
            fun a b => Classical.propDecidable (a = b)
          rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL
            programs function]
          rw [fupdateListHOL_eq]
          exact flookup_fupdateList_reverse_of_mem _ _ _ hentries hmakeEntry
        refine ⟨firstLoopName + index, sourceParameters.length, ?_, rfl, ?_⟩
        · change (crepToLoopMakeFuncsExactHOL programs).lookup function = _
          exact hmake
        · show sptLookup (firstLoopName + index)
            (sptFromAList (compileProgHOLExact target programs)) = _
          rw [memLookupFromAListSomeExact
            (firstCompileProgAllDistinctExact target programs)]
          have hbound : index < (compileProgHOLExact target programs).length := by
            simp [compileProgHOLExact, hindex]
          have hget : (compileProgHOLExact target programs)[index]'hbound =
              (firstLoopName + index, List.range sourceParameters.length,
                ocompileHOLExact
                  (ctxtFcExact target (crepToLoopMakeFuncsExactHOL programs)
                    sourceParameters (List.range sourceParameters.length))
                  (listToNumSetHOLExact (List.range sourceParameters.length))
                  (crepSimpProgHOL sourceProgram)) := by
            simp only [compileProgHOLExact, List.getElem_zipWith,
              List.getElem_map, List.getElem_range, hsourceEntry]
            simp only [compFuncHOLExact, ocompileHOLExact,
              Prod.mk.injEq, true_and]
            refine ⟨Nat.add_comm _ _, ?_⟩
            rw [compFuncContextEqCtxtFcExact target programs sourceParameters]
          have hcompiledMem := List.getElem_mem hbound
          rw [hget] at hcompiledMem
          exact hcompiledMem

end Flapjack
