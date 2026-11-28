module

public import Flapjack.HOL.Transfer.Relation
public import Flapjack.HOL.Transfer.Fmsp.Domain
public import Flapjack.Misc.Option.Rel
public import Flapjack.Compiler.Inference.Unify.Machine

@[expose] public section

/-!
# The unify transfer relation `RKC` is surjective

Counterpart of `surj_RKC` from `cakeml/compiler/inference/unifyScript.sml`. The
relation itself (`RKC_def`) is ported in `Unify/Machine.lean`; this module adds
the surjectivity law over the reviewed transfer relation.
-/

namespace Flapjack.Compiler.Inference.Unify

open Flapjack.HOL.Transfer.Relation Flapjack.HOL.Transfer.Fmsp Flapjack.HOL.Unification

/-- Original `surj_RKC`: every inference type is related to its encoding. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "surj_RKC"]
theorem surjRkc : surj rkc := by
  intro ct
  exact ⟨encodeInferT ct, rfl⟩

/-- Mapping the values of a finite map keeps its domain. -/
private theorem domainMap2 {α β γ : Type} (f : α × β → γ)
    (map : HolFiniteMapExact α β) : (map.map2 f).domain = map.domain := by
  funext key
  apply propext
  show (map.map2 f).lookup key ≠ none ↔ map.lookup key ≠ none
  rw [HolFiniteMapExact.lookup_map2]
  cases found : map.lookup key with
  | none => simp
  | some value => simp

/-- The converted map has exactly the sparse tree's domain. -/
private theorem domainSp2fm {α : Type} (tree : Spt α) :
    (sp2fm tree).domain = {key | sptDomain tree key} := by
  funext key
  apply propext
  show sptLookup key tree ≠ none ↔ sptDomain tree key
  rw [sptDomain_iff_lookup]
  constructor
  · intro hne
    cases found : sptLookup key tree with
    | none => exact absurd found hne
    | some value => exact ⟨value, rfl⟩
  · intro hex
    obtain ⟨value, hvalue⟩ := hex
    rw [hvalue]
    exact Option.some_ne_none value

/-- Original `substR_FDOM`: the encoded substitution and the inference
substitution have the same domain. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "substR_FDOM"]
theorem substRFdom :
    funRel substR (· = ·) HolFiniteMapExact.domain (fun sp => {key | sptDomain sp key}) := by
  intro fm sp hsub
  show fm.domain = {key | sptDomain sp key}
  rw [hsub.2.2, domainMap2, domainSp2fm]

/-- Original `substR_FLOOKUP`: lookup in the encoded substitution and in the
inference substitution agree through `RKC`. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "substR_FLOOKUP"]
theorem substRFlookup :
    funRel substR (funRel (· = ·) (optionRel rkc)) (fun fm => fm.lookup)
      (fun sp key => sptLookup key sp) := by
  intro fm sp hsub key y heq
  subst heq
  show optionRel rkc (fm.lookup key) (sptLookup key sp)
  rw [hsub.2.2, HolFiniteMapExact.lookup_map2,
    holFmapAsFiniteSupportResultWitness_sp2fm]
  cases found : sptLookup key sp with
  | none => trivial
  | some value => rfl

/-- Original `substR_RFORALL`: a bounded universal quantification transfers
from encoded substitutions to inference substitutions. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "substR_RFORALL"]
theorem substRForall :
    funRel (fun P Q => ∀ fm sp, substR fm sp → (P fm → Q sp)) (fun p q => p → q)
      (resForall wfs) (resForall cwfs) := by
  intro P Q hrel hall sp hcwfs
  have hwfs : wfs ((sp2fm sp).map2 (fun p => encodeInferT p.2)) := by
    have hsw : swfs (sptMap encodeInferT sp) := hcwfs.1
    simp only [swfs, sp2fm_map] at hsw
    exact hsw
  have hsub : substR ((sp2fm sp).map2 (fun p => encodeInferT p.2)) sp :=
    ⟨hwfs, hcwfs.2, rfl⟩
  exact hrel _ sp hsub (hall _ hwfs)

end Flapjack.Compiler.Inference.Unify
