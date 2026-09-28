import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-!
# crep_to_loop `code_rel2_def` and `mk_ctxt_code_imp_code_rel2`

Exact ports of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`code_rel2_def` (3842) and `mk_ctxt_code_imp_code_rel2` (3861) over the exact
carriers (bead `flapjack-pxn.18.5.6.33.22`).  `FMAP_MAP2` is
`HolFiniteMapExact.map2`, `crep_arith$simp_prog` the tagged `crepSimpProgHOL`,
`code_rel` the tagged exact `crepToLoopCodeRelExact`, `mk_ctxt` the tagged
`mkCtxtExact`, `compile_prog` the tagged `compileProgHOLExact`, `make_funcs` at
the exact finite-map carrier the untagged `crepToLoopMakeFuncsExactHOL` used by
`compileProgHOLExact`, `fromAList` is `sptFromAList`, and HOL `alist_to_fmap`
is `alistToFmapCodeExact` below.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

/-! Same-module relation witness for `code_rel2_def`'s `CrepToLoopContextExact`
carrier (its traversed `funcs` field); the standalone `s_code` parameter is
validated at its `HolFiniteMapExact` binder. -/
namespace CrepToLoopCodeRel2Witnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCodeRel2Witnesses

/-- Exact HOL `code_rel2_def` (`crep_to_loopProofScript.sml:3842-3845`):
    `code_rel2 ctxt s_code t_code <=>
      code_rel ctxt (FMAP_MAP2 (\(s, n, p). (n,crep_arith$simp_prog p)) s_code) t_code`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel2_def"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.funcs, s_code])
  (words_as_type_indexed_bitvec)]
def crepToLoopCodeRel2Exact {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width)) : Prop :=
  crepToLoopCodeRelExact ctxt
    (s_code.map2 (fun entry => match entry with | (_, n, p) => (n, crepSimpProgHOL p))) t_code

/-- Flapjack rendering (no CakeML declaration; HOL `alistTheory.alist_to_fmap`)
    of `alist_to_fmap` on the code carrier: `FOLDR` of `|+`, i.e. the first
    occurrence of a key wins. -/
def alistToFmapCodeExact {width : Nat} [NeZero width]
    (entries : List (MlString × List Nat × CrepProgHOL width)) :
    HolFiniteMapExact MlString (List Nat × CrepProgHOL width) :=
  HolFiniteMapExact.empty.updateList entries.reverse

private theorem fupdateListHOL_eq {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (f : FiniteMap α β),
      FUPDATE_LIST_HOL f entries = FUPDATE_LIST f entries
  | [], _ => rfl
  | e :: es, f => by
      simp only [FUPDATE_LIST_HOL, FUPDATE_LIST, List.foldl_cons]
      have : FUPDATE_HOL f e = FUPDATE f e := by
        funext k
        simp only [FUPDATE_HOL, FUPDATE]
        by_cases h : k = e.1
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [this]
      exact fupdateListHOL_eq es _

private theorem flookup_fupdateList_reverse_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), (l.map Prod.fst).Nodup → (k, v) ∈ l →
      FLOOKUP (FUPDATE_LIST FEMPTY l.reverse) k = some v
  | [], _, _, _, h => by simp at h
  | a :: t, k, v, hd, h => by
      simp only [List.reverse_cons, FUPDATE_LIST, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      simp only [FLOOKUP, FUPDATE]
      rw [List.map_cons] at hd
      have hd' := List.nodup_cons.mp hd
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have hne : a.1 ≠ k := fun e => hd'.1 (e ▸ List.mem_map_of_mem h)
        simp only [beq_iff_eq, hne, if_false]
        exact flookup_fupdateList_reverse_of_mem t k v hd'.2 h

private theorem flookup_fupdateList_reverse_mem' {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β),
      FLOOKUP (FUPDATE_LIST FEMPTY l.reverse) k = some v → (k, v) ∈ l
  | [], k, v, h => by simp [FUPDATE_LIST, FLOOKUP, FEMPTY] at h
  | a :: t, k, v, h => by
      simp only [List.reverse_cons, FUPDATE_LIST, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at h
      simp only [FLOOKUP, FUPDATE] at h
      split at h
      · rename_i hk
        cases h
        have : a.1 = k := LawfulBEq.eq_of_beq hk
        subst this
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (flookup_fupdateList_reverse_mem' t k v h)

private theorem holFiniteMapExact_ext {α β : Type} {m1 m2 : HolFiniteMapExact α β}
    (h : m1.lookup = m2.lookup) : m1 = m2 := by
  cases m1; cases m2; simp only at h; subst h; rfl

private theorem foldr_max_range (n : Nat) : (List.range n).foldr max 0 = n - 1 := by
  have key : ∀ a, (List.range n).foldr max a = if n = 0 then a else max a (n - 1) := by
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [ih]
      split <;> simp_all <;> omega
  rw [key]; split <;> omega

private theorem makeFuncsExact_lookup {width : Nat} [NeZero width]
    (prog : List (MlString × List Nat × CrepProgHOL width)) :
    (crepToLoopMakeFuncsExactHOL prog).lookup = FLOOKUP (crepToLoopMakeFuncsHOL prog) := by
  funext k
  simp only [crepToLoopMakeFuncsExactHOL, crepToLoopMakeFuncsHOL,
    HolFiniteMapExact.lookup_updateListEq, FLOOKUP, fupdateListHOL_eq]
  rfl

/-- Exact HOL `mk_ctxt_code_imp_code_rel2` (`crep_to_loopProofScript.sml:3861-3866`):
    `!c crep_code start np. ALL_DISTINCT (MAP FST crep_code) /\
      ALOOKUP crep_code start = SOME ([],np) ==>
      code_rel2 (mk_ctxt c FEMPTY (make_funcs crep_code) 0)
        (alist_to_fmap crep_code) (fromAList (crep_to_loop$compile_prog c crep_code))`.
    The finite maps occur only as values of the tagged exact definitions
    (`mk_ctxt`, `make_funcs`, `alist_to_fmap`), none as a binder, so as for
    `compile_prog_def` only the words qualifier applies. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mk_ctxt_code_imp_code_rel2"
  (words_as_type_indexed_bitvec)]
theorem mk_ctxt_code_imp_code_rel2 {width : Nat} [NeZero width] :
    ∀ (c : AsmArchitecture) (crep_code : List (MlString × List Nat × CrepProgHOL width))
      (start : MlString) (np : CrepProgHOL width),
      (crep_code.map Prod.fst).Nodup ∧ holAlookup crep_code start = some ([], np) →
      crepToLoopCodeRel2Exact
        (mkCtxtExact c HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL crep_code) 0)
        (alistToFmapCodeExact crep_code) (sptFromAList (compileProgHOLExact c crep_code)) := by
  intro c crep_code start np ⟨hd, _⟩
  refine ⟨?_, ?_⟩
  · show crepToLoopDistinctFuncs (crepToLoopMakeFuncsExactHOL crep_code).lookup
    rw [makeFuncsExact_lookup]
    exact distinct_make_funcs crep_code
  · intro f ns prog hf
    simp only [HolFiniteMapExact.lookup_map2] at hf
    cases hsrc : (alistToFmapCodeExact crep_code).lookup f with
    | none => simp [hsrc] at hf
    | some val =>
    obtain ⟨ns0, p0⟩ := val
    simp only [hsrc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have hmem : (f, ns0, p0) ∈ crep_code := flookup_fupdateList_reverse_mem' _ _ _ hsrc
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hmem
    have hentries : (((crep_code.zip (List.range crep_code.length)).map
        (fun entry => (entry.1.1, (firstLoopName + entry.2, entry.1.2.1.length)))).map
          Prod.fst).Nodup := by
      have : ((crep_code.zip (List.range crep_code.length)).map
          (fun entry => (entry.1.1, (firstLoopName + entry.2, entry.1.2.1.length)))).map
            Prod.fst = crep_code.map Prod.fst := by
        rw [List.map_map]
        change List.map (Prod.fst ∘ Prod.fst) _ = _
        rw [← List.map_map, List.map_fst_zip (by simp)]
      rw [this]; exact hd
    have hlen : i < (List.range crep_code.length).length := by simpa using hi
    refine ⟨firstLoopName + i, ns0.length, ?_, rfl, ?_⟩
    · show (crepToLoopMakeFuncsExactHOL crep_code).lookup f = _
      rw [makeFuncsExact_lookup]
      apply flookup_fupdateList_reverse_of_mem _ _ _ hentries
      apply List.mem_map.mpr
      refine ⟨(crep_code[i], i), ?_, by simp [hei]⟩
      have hz : i < (crep_code.zip (List.range crep_code.length)).length := by simpa using hi
      have := List.getElem_mem hz
      simpa [List.getElem_zip] using this
    · show sptLookup (firstLoopName + i) (sptFromAList (compileProgHOLExact c crep_code)) = _
      rw [memLookupFromAListSomeExact (first_compile_prog_all_distinct c crep_code)]
      have hz : i < (compileProgHOLExact c crep_code).length := by
        simp [compileProgHOLExact, hi]
      have := List.getElem_mem hz
      have hget : (compileProgHOLExact c crep_code)[i]'hz =
          (firstLoopName + i, List.range ns0.length,
            ocompileHOLExact
              (ctxtFcExact c (crepToLoopMakeFuncsExactHOL crep_code) ns0 (List.range ns0.length))
              (listToNumSetHOLExact (List.range ns0.length)) (crepSimpProgHOL p0)) := by
        simp only [compileProgHOLExact, List.getElem_zipWith, List.getElem_map,
          List.getElem_range, hei]
        simp only [compFuncHOLExact, ocompileHOLExact, Prod.mk.injEq, true_and]
        refine ⟨Nat.add_comm _ _, ?_⟩
        congr 2
        simp only [mkCtxtExact, ctxtFcExact, makeVmapExact, foldr_max_range]
        congr 1
        apply holFiniteMapExact_ext
        funext k
        simp only [HolFiniteMapExact.lookup_updateListEq, fupdateListHOL_eq]
        rfl
      rw [hget] at this
      exact this

end Flapjack
