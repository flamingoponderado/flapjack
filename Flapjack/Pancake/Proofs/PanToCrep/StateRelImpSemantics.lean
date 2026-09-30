import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.PanToCrep.ContextExact

/-!
# pan_to_crep whole-program semantics: entry-context lemmas

Counterparts of `cakeml/pancake/proofs/pan_to_crepProofScript.sml:4656-4682`
(bead `flapjack-pxn.18.4.4.2`).  HOL `state_rel_imp_semantics_to_crep` uses
these lemmas to establish `excp_rel` and `locals_rel` for its entry context
`mk_ctxt FEMPTY (make_funcs …) 0 (get_eids_from_decls …)`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanToCrepStateRelImpSemanticsWitnesses

/-- Same-module roundtrip for the relation qualifier's context carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

end PanToCrepStateRelImpSemanticsWitnesses

/-- An entry of the `get_eids_from_decls` association list is an exception
    name paired with the word code of its index. -/
private theorem getEidsEntriesHOL_mem {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (entry : MlS × BitVec width)
    (h : entry ∈ getEidsEntriesHOL decls) :
    ∃ i, i < sizeOfEidsHOL decls ∧
      ∃ hi : i < ((exceptionsHOL decls).map Prod.fst).length,
        entry = (((exceptionsHOL decls).map Prod.fst)[i], BitVec.ofNat width i) := by
  unfold getEidsEntriesHOL at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_zip, List.length_map, List.length_range, Nat.lt_min] at hi
  refine ⟨i, hi.2, by simpa using hi.1, ?_⟩
  simp [List.getElem_zip]

/-- Exact HOL `get_eids_imp_excp_rel` (`pan_to_crepProofScript.sml:4656-4660`):

    ```
    !seids (pc:'a decl list).
      panLang$size_of_eids pc < dimword (:'a) /\
      FDOM seids = FDOM (get_eids_from_decls pc) ==>
        excp_rel (get_eids_from_decls pc) seids
    ```

    HOL `dimword (:'a)` is `2 ^ width`, and `FDOM` equality is pointwise
    definedness of the canonical finite-map lookups, as in the tagged
    `excp_rel_def`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "get_eids_imp_excp_rel"
  (fmap_as_finite_support_relation := [seids]) (words_as_type_indexed_bitvec)]
theorem getEidsImpExcpRelExact {width : Nat} [NeZero width] :
    ∀ (seids : HolFiniteMapExact MlS ShapeHOL) (pc : List (DeclHOL width)),
      sizeOfEidsHOL pc < 2 ^ width ∧
        (∀ key, (seids.lookup key).isSome = ((getEidsFromDeclsHOL pc).lookup key).isSome) →
      panToCrepExcpRelFiniteExact (getEidsFromDeclsHOL pc) seids := by
  intro seids pc ⟨hsize, hdom⟩
  refine ⟨hdom, ?_⟩
  intro e e' n n' he he' hnn
  obtain ⟨entry, hmem, hkey, hval⟩ :=
    flookupAlistToFmap_mem (getEidsEntriesHOL pc) e n he
  obtain ⟨entry', hmem', hkey', hval'⟩ :=
    flookupAlistToFmap_mem (getEidsEntriesHOL pc) e' n' he'
  obtain ⟨i, hi, hil, rfl⟩ := getEidsEntriesHOL_mem pc entry hmem
  obtain ⟨j, hj, hjl, rfl⟩ := getEidsEntriesHOL_mem pc entry' hmem'
  simp only at hkey hval hkey' hval'
  subst hkey hkey' hval hval'
  have hij : i = j := by
    have h := congrArg BitVec.toNat hnn
    simp only [BitVec.toNat_ofNat] at h
    rwa [Nat.mod_eq_of_lt (Nat.lt_trans hi hsize), Nat.mod_eq_of_lt (Nat.lt_trans hj hsize)] at h
  subst hij
  rfl

/-- Exact HOL `mk_ctxt_imp_locals_rel` (`pan_to_crepProofScript.sml:4677-4679`):
    `!pc lcl es. locals_rel (mk_ctxt FEMPTY (make_funcs pc) 0 es) FEMPTY lcl`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mk_ctxt_imp_locals_rel"
  (fmap_as_finite_support_relation := [PanToCrepContextExact.vars, lcl, es])
  (words_as_type_indexed_bitvec)]
theorem mkCtxtImpLocalsRelExact {width : Nat} [NeZero width] :
    ∀ (pc : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (lcl : HolFiniteMapExact Nat (HolWordLab width))
      (es : HolFiniteMapExact MlS (BitVec width)),
      panToCrepLocalsRelFiniteExact
        (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL pc) 0 es)
        HolFiniteMapExact.empty lcl := by
  intro pc lcl es
  refine ⟨⟨?_, ?_⟩, ⟨Nat.zero_le _, ?_⟩, ?_⟩ <;>
    intros <;> simp_all [mkCtxtExactHOL, HolFiniteMapExact.empty]

end Flapjack
