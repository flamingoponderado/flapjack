module

public import Flapjack.Compiler.Inference.EnvRel.Approx
public import Flapjack.Compiler.Inference.Unify.Walkstar.Empty

@[expose] public section

/-! Declarative scheme instantiation and inference approximation. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.Unify

/-- At the empty substitution, both normalizers are the identity, so the
    approximation model agrees with the source relation at this application. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tscheme_inst_to_approx"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem tschemeInstToApprox (tvs : Nat) (t : SemanticT) (tvs' : Nat) (t' : SemanticT)
    (h : tschemeInst (tvs, t) (tvs', t')) :
    tschemeApproxModel 0 HolFiniteMapExact.holEmpty (tvs, unconvertT t) (tvs', unconvertT t') := by
  obtain ⟨subst, len, checked, allChecked, same⟩ := h
  refine ⟨subst.map unconvertT, by simpa using len, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have cy : checkFreevars tvs [] y = true := (List.all_eq_true.mp allChecked) y hy
    have ct := checkFreevarsToCheckT tvs y () cy
    change Infer.checkT (0 + tvs) HolFiniteMapExact.holEmpty.domain (unconvertT y)
    have domainEmpty : (HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat InferT).domain =
        (fun _ => False) := by
      funext key
      apply propext
      change (none : Option InferT) ≠ none ↔ False
      simp
    simpa [domainEmpty] using ct
  · intro inst instLen
    simp only [tWalkstarEmpty]
    have unconverted := unconvertDbSubst t' subst () tvs' checked
    rw [same] at unconverted
    rw [unconverted]
    have checked' : Infer.checkT (subst.map unconvertT).length (fun _ => False) (unconvertT t') := by
      simpa [len] using checkFreevarsToCheckT tvs' t' () checked
    have composed := (inferDeBruijnSubstTwice inst (subst.map unconvertT) (fun _ => False)).1
      (unconvertT t') checked'
    simpa [List.map_map, Function.comp_def] using composed

end Flapjack.Compiler.Inference.EnvRel
