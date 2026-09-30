import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-! Code-map permutation prerequisites of the PanGlobals semantics proof.
The code map is canonical finite-support; declaration and program payloads
use the already reviewed MlS/ProgHOL/ShapeHOL carriers. -/

namespace Flapjack

open Pancake.PanLang

/-- Independent raw lookup rendering of HOL's FUN_FMAP equation: its domain
is the preimage of the source domain, and each defined payload keeps its
parameters/return shape while renaming the body. Flapjack codec infrastructure,
not an independently tagged HOL declaration over unrestricted maps. -/
def fpermCodeRaw {width : Nat} [NeZero width] (f g : MlS)
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) : Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :=
  (code (fpermName f g name)).map fun entry =>
    (entry.1, fpermHOL f g entry.2.1, entry.2.2)

/-- HOL fperm_code: involutive key swap and body renaming on the canonical
finite-map carrier. Mapping the finite source support through the same swap
establishes precisely the finite preimage used by HOL's FUN_FMAP. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_code_def"
  (fmap_as_finite_support_result) (words_as_type_indexed_bitvec)]
def fpermCodeHOL {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) where
  lookup name := (code.lookup (fpermName f g name)).map fun entry =>
    (entry.1, fpermHOL f g entry.2.1, entry.2.2)
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := code.finiteSupport
    refine ⟨keys.map (fpermName f g), ?_⟩
    intro name h
    have hs : code.lookup (fpermName f g name) ≠ none := by
      intro hn
      simp [hn] at h
    exact List.mem_map.mpr ⟨fpermName f g name, hkeys _ hs, fpermName_cancel f g name⟩

/-- Flapjack-specific lookup codec witness against the independent raw HOL
FUN_FMAP rendering. Neither a target correspondence premise nor a self-equality. -/
theorem holFmapAsFiniteSupportResultWitness_fpermCodeHOL
    {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) :
    (fpermCodeHOL f g code).lookup name = fpermCodeRaw f g code.lookup name := rfl

@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FLOOKUP_fperm_code'"
  (fmap_as_finite_support_relation := [code]) (words_as_type_indexed_bitvec)]
theorem flookupFpermCodeHOL' {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) :
    (fpermCodeHOL f g code).lookup name =
      (code.lookup (fpermName f g name)).map (fun entry =>
        (entry.1, fpermHOL f g entry.2.1, entry.2.2)) := rfl

@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FLOOKUP_fperm_code"
  (fmap_as_finite_support_relation := [code]) (words_as_type_indexed_bitvec)]
theorem flookupFpermCodeHOL {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) :
    (fpermCodeHOL f g code).lookup (fpermName f g name) =
      (code.lookup name).map (fun entry =>
        (entry.1, fpermHOL f g entry.2.1, entry.2.2)) := by
  simp only [flookupFpermCodeHOL', fpermName_cancel]

/-- Source comparison, flapjack-ds10 (2026-09-30, bead
`flapjack-pxn.18.5.2.22.4.3`). Exact port of HOL `fperm_code_FEMPTY`
(`cakeml/pancake/proofs/pan_globalsProofScript.sml:1657`):
`fperm_code f g FEMPTY = FEMPTY`. The whole statement is a single
`HolFiniteMapExact` map equality, so it carries the dedicated singular
`(fmap_as_finite_support_equality)` qualifier, witnessed at the lookup level by
`holFmapAsFiniteSupportEqualityWitness_fpermCodeHOL_empty`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_code_FEMPTY"
  (fmap_as_finite_support_equality) (words_as_type_indexed_bitvec)]
theorem fpermCodeHOL_empty {width : Nat} [NeZero width] (f g : MlS) :
    fpermCodeHOL f g
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) = HolFiniteMapExact.empty := by
  apply HolFiniteMapExact.ext
  funext name
  rfl

/-- Unconditional lookup-level witness for `fpermCodeHOL_empty`: both sides
agree at the same universally bound key `name`. -/
theorem holFmapAsFiniteSupportEqualityWitness_fpermCodeHOL_empty
    {width : Nat} [NeZero width] (f g : MlS) (name : MlS) :
    (fpermCodeHOL f g
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))).lookup name =
      HolFiniteMapExact.empty.lookup name := by
  rw [fpermCodeHOL_empty]

@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_append"
  (words_as_type_indexed_bitvec)]
theorem fpermDecsHOL_append {width : Nat} [NeZero width] (f g : MlS)
    (xs ys : List (DeclHOL width)) :
    fpermDecsHOL f g (xs ++ ys) = fpermDecsHOL f g xs ++ fpermDecsHOL f g ys := by
  induction xs with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih => cases d <;> simp [fpermDecsHOL, ih]

/-- Flapjack-specific update factoring for the universal update-list proof.
HOL has no standalone declaration for this single-update helper. -/
theorem fpermCodeHOL_updateEq {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (entry : MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :
    fpermCodeHOL f g (code.updateEq entry) =
      (fpermCodeHOL f g code).updateEq
        (fpermName f g entry.1, entry.2.1, fpermHOL f g entry.2.2.1, entry.2.2.2) := by
  apply HolFiniteMapExact.ext
  funext name
  by_cases h : name = fpermName f g entry.1
  · subst name
    simp [fpermCodeHOL, HolFiniteMapExact.updateEq, FUPDATE_HOL, fpermName_cancel]
  · have hn : fpermName f g name ≠ entry.1 := by
      intro heq
      apply h
      have hc := congrArg (fpermName f g) heq
      simpa only [fpermName_cancel] using hc
    simp [fpermCodeHOL, HolFiniteMapExact.updateEq, FUPDATE_HOL, h, hn]

/-- Flapjack-specific list-update factoring, stronger than HOL's
functions-only instance. No HOL tag: the source theorem restricts entries to
the function table of a declaration list. -/
theorem fpermCodeHOL_updateListEq {width : Nat} [NeZero width] (f g : MlS)
    (fm : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    fpermCodeHOL f g (fm.updateListEq entries) =
      (fpermCodeHOL f g fm).updateListEq
        (entries.map fun entry =>
          (fpermName f g entry.1, entry.2.1, fpermHOL f g entry.2.2.1, entry.2.2.2)) := by
  induction entries generalizing fm with
  | nil => rfl
  | cons entry entries ih =>
      change fpermCodeHOL f g ((fm.updateEq entry).updateListEq entries) =
        ((fpermCodeHOL f g fm).updateEq
          (fpermName f g entry.1, entry.2.1, fpermHOL f g entry.2.2.1, entry.2.2.2)).updateListEq _
      rw [ih, fpermCodeHOL_updateEq]

@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_code_FUPDATE_LIST_functions"
  (fmap_as_finite_support_relation := [fm]) (words_as_type_indexed_bitvec)]
theorem fpermCodeHOL_updateList_functions {width : Nat} [NeZero width] (f g : MlS)
    (fm : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (code : List (DeclHOL width)) :
    fpermCodeHOL f g (fm.updateListEq (functionsHOL code)) =
      (fpermCodeHOL f g fm).updateListEq (functionsHOL (fpermDecsHOL f g code)) := by
  rw [functionsFpermDecsHOL]
  exact fpermCodeHOL_updateListEq f g fm (functionsHOL code)

/-- Exact HOL `lookup_code_fperm_code`: code/body/name permutation leaves
parameter validation and the returned callee locals and return shape unchanged.
The canonical lookup used here is the executed faithful Call/DecCall entry. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "lookup_code_fperm_code"
  (fmap_as_finite_support_relation := [code]) (words_as_type_indexed_bitvec)]
theorem lookupCodeFpermCodeHOL {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) (args : List (ValueHOL width)) :
    PanSemStateFiniteExact.lookupCodeCanonicalHOL (fpermCodeHOL f g code) (fpermName f g name) args =
      (PanSemStateFiniteExact.lookupCodeCanonicalHOL code name args).map (fun entry =>
        (fpermHOL f g entry.1, entry.2.1, entry.2.2)) := by
  have hraw : lookupCodeHOLExact (fpermCodeHOL f g code).lookup (fpermName f g name) args =
      (lookupCodeHOLExact code.lookup name args).map (fun entry =>
        (fpermHOL f g entry.1, entry.2.1, entry.2.2)) := by
    unfold lookupCodeHOLExact
    rw [flookupFpermCodeHOL]
    cases h : code.lookup name with
    | none => simp
    | some entry =>
        obtain ⟨params, body, shape⟩ := entry
        simp only [Option.map_some]
        split <;> simp_all
  let project := fun (entry : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) =>
    (entry.1, entry.2.1.lookup, entry.2.2)
  have hinj : Function.Injective project := by
    rintro ⟨p1,l1,s1⟩ ⟨p2,l2,s2⟩ h
    simp only [project, Prod.mk.injEq] at h
    obtain ⟨rfl, hl, rfl⟩ := h
    have hm : l1 = l2 := HolFiniteMapExact.ext hl
    subst l2
    rfl
  apply Option.map_injective hinj
  rw [PanSemStateFiniteExact.holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeCanonicalHOL]
  rw [Option.map_map]
  change _ = Option.map ((fun (entry : ProgHOL width × (MlS → Option (ValueHOL width)) × ShapeHOL) =>
    (fpermHOL f g entry.1, entry.2.1, entry.2.2)) ∘ project)
      (PanSemStateFiniteExact.lookupCodeCanonicalHOL code name args)
  rw [← Option.map_map]
  rw [PanSemStateFiniteExact.holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeCanonicalHOL]
  exact hraw

end Flapjack
