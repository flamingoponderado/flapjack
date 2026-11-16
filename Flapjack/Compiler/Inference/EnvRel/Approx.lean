module

public import Flapjack.Compiler.Inference.EnvRel
public import Flapjack.Compiler.Inference.Unify.Walkstar
public import Flapjack.Compiler.Inference.InferProps.DeBruijn.PreservesCheck
public import Flapjack.Compiler.Inference.InferProps.CheckMonotone
public import Flapjack.Compiler.Inference.InferProps.DeBruijn.Compose

@[expose] public section

/-! Source-shaped approximation for inference type schemes. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.Unify

/-- Source-shaped scheme approximation. This remains untagged: `tWalkstar`
    agrees with the source equations on well-formed substitutions, but its
    off-guard choice is not established as HOL’s chosen value. -/
noncomputable def tschemeApproxModel (maxTvs : Nat) (s : HolFiniteMapExact Nat InferT)
    (left right : Nat × InferT) : Prop :=
  ∃ subst : List InferT, subst.length = right.1 ∧
    (∀ t ∈ subst, checkT (maxTvs + left.1) s.domain t) ∧
    ∀ inst : List InferT, inst.length = left.1 →
      tWalkstar s (inferDeBruijnSubst inst left.2) =
      tWalkstar s (inferDeBruijnSubst (subst.map (inferDeBruijnSubst inst)) right.2)

/-- The source-shaped approximation is reflexive. This is a model theorem:
    the underlying off-guard normalizer choice is not yet a reviewed HOL port. -/
theorem tschemeApproxModelRefl (maxTvs : Nat) (s : HolFiniteMapExact Nat InferT)
    (tvs : Nat) (t : InferT) : tschemeApproxModel maxTvs s (tvs, t) (tvs, t) := by
  refine ⟨(List.range tvs).map InferT.varDb, by simp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    apply (checkT_varDb (maxTvs + tvs) i s.domain).2
    omega
  · intro inst length
    have ident : ((List.range tvs).map InferT.varDb).map (inferDeBruijnSubst inst) = inst := by
      apply List.ext_getElem
      · simpa using length.symm
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_range]
        have hi : i < inst.length := hi2
        simp [inferDeBruijnSubst, hi]
    rw [ident]

/-- The source approximation’s instantiation property for the model. It is
    untagged until its normalizer is related to HOL at the definition boundary. -/
theorem tschemeApproxModelThm (t2 : InferT) (maxTvs : Nat)
    (s : HolFiniteMapExact Nat InferT) (tvs tvs2 : Nat) (t : InferT)
    (_hw : tWfs s) (ha : tschemeApproxModel maxTvs s (tvs, t) (tvs2, t2)) :
    ∀ inst : List InferT, inst.length = tvs ∧ (∀ x ∈ inst, checkT maxTvs (fun _ => False) x) →
      ∃ subst : List InferT, subst.length = tvs2 ∧ (∀ x ∈ subst, checkT maxTvs s.domain x) ∧
        tWalkstar s (inferDeBruijnSubst inst t) = tWalkstar s (inferDeBruijnSubst subst t2) := by
  intro inst hi
  obtain ⟨subst, len, checked, equal⟩ := ha
  refine ⟨subst.map (inferDeBruijnSubst inst), by simpa using len, ?_, equal inst hi.1⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  apply checkTInferDeBruijnSubst inst y maxTvs s.domain
  constructor
  · simpa [hi.1] using checked y hy
  · intro x hx
    exact checkTMore5.1 x (fun _ => False) maxTvs (hi.2 x hx) s.domain (by intro v impossible; cases impossible)

/-- Transitivity of scheme approximation in the source-shaped model. The
    normalizer's off-guard choice remains unreviewed, so this is untagged. -/
theorem tschemeApproxModelTrans (maxTvs : Nat) (s : HolFiniteMapExact Nat InferT)
    (tvs1 : Nat) (t1 : InferT) (tvs2 : Nat) (t2 : InferT) (tvs3 : Nat) (t3 : InferT)
    (h : tschemeApproxModel maxTvs s (tvs1, t1) (tvs2, t2) ∧
      tschemeApproxModel 0 s (tvs2, t2) (tvs3, t3)) :
    tschemeApproxModel maxTvs s (tvs1, t1) (tvs3, t3) := by
  obtain ⟨xs, hxs, checks, first⟩ := h.1
  obtain ⟨ys, hys, checkys, second⟩ := h.2
  refine ⟨ys.map (inferDeBruijnSubst xs), by simpa using hys, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    apply checkTInferDeBruijnSubst xs y (maxTvs + tvs1) s.domain
    constructor
    · have hy' := checkTMore2.1 y tvs2 s.domain (by simpa using checkys y hy) (maxTvs + tvs1)
      simpa [hxs] using hy'
    · exact checks
  · intro inst hi
    have hfirst := first inst hi
    have hsecond := second (xs.map (inferDeBruijnSubst inst)) (by simpa using hxs)
    rw [hfirst, hsecond]
    congr 1
    have heq : (ys.map (inferDeBruijnSubst xs)).map (inferDeBruijnSubst inst) =
        ys.map (inferDeBruijnSubst (xs.map (inferDeBruijnSubst inst))) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro y hy
      apply (inferDeBruijnSubstTwice inst xs s.domain).1 y
      simpa [hxs] using checkys y hy
    rw [heq]

end Flapjack.Compiler.Inference.EnvRel
