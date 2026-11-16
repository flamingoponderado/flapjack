module

public import Flapjack.Compiler.Inference.EnvRel
public import Flapjack.Compiler.Inference.Unify.Walkstar
public import Flapjack.Compiler.Inference.InferProps.DeBruijn.PreservesCheck
public import Flapjack.Compiler.Inference.InferProps.CheckMonotone

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

end Flapjack.Compiler.Inference.EnvRel
