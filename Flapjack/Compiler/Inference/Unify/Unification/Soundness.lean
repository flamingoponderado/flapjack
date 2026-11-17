module

public import Flapjack.Compiler.Inference.Unify.EncodingInvariant
public import Flapjack.HOL.Unification.UnifProps.Soundness

@[expose] public section

/-! Soundness of inference-type unification through the first-order model. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Full soundness of the inference unifier model: a successful result is
    well formed, extends the input, and normalizes both inputs equally. This
    is not tagged as HOL t_unify_unifier until the optional finite-map result
    and the selected source unifier have a reviewed representation. -/
theorem tUnifyModelSound (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT)
    (sx : HolFiniteMapExact Nat InferT) (h : tWfs s ∧ tUnifyModel s t1 t2 = some sx) :
    tWfs sx ∧ s.submap sx ∧ tWalkstar sx t1 = tWalkstar sx t2 := by
  have aux := encodeUnifyModelAll 0 (encodeSubst s) (encodeInferT t1) (encodeInferT t2)
    s t1 t2 ⟨rfl, Or.inl ⟨rfl, rfl⟩, h.1⟩
  rw [h.2] at aux
  simp only [Option.map_some] at aux
  have sound := tunifyAuxSound _ _ _ _ ⟨h.1, aux⟩
  refine ⟨sound.1, ?_, ?_⟩
  · intro k v found
    have encoded : (encodeSubst s).lookup k = some (encodeInferT v) := by
      simp [encodeSubst, HolFiniteMapExact.lookup_map2, found]
    have mapped := sound.2.1 k (encodeInferT v) encoded
    cases target : sx.lookup k with
    | none => simp [encodeSubst, HolFiniteMapExact.lookup_map2, target] at mapped
    | some value =>
      simp only [encodeSubst, HolFiniteMapExact.lookup_map2, target, Option.map_some,
        Option.some.injEq] at mapped
      have same := congrArg decodeInferT mapped
      simpa [decodeLeftInverse.1] using same
  · unfold tWalkstar
    exact congrArg decodeInferT sound.2.2

end Flapjack.Compiler.Inference.Unify
