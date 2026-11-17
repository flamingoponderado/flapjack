module

public import Flapjack.Compiler.Inference.Unify.Unification.MostGeneral
public import Flapjack.HOL.Unification.UnifProps.Complete

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Completeness of the inference unifier model. It remains untagged until
    the option-wrapped finite-map result has a reviewed representation. -/
theorem tUnifyModelComplete (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT)
    (s2 : HolFiniteMapExact Nat InferT)
    (h : tWfs s ∧ tWfs s2 ∧ tWalkstar s2 (tWalkstar s t1) = tWalkstar s2 (tWalkstar s t2)) :
    ∃ sx, tUnifyModel s t1 t2 = some sx := by
  have eq : walkstar (encodeSubst s2) (walkstar (encodeSubst s) (encodeInferT t1)) =
      walkstar (encodeSubst s2) (walkstar (encodeSubst s) (encodeInferT t2)) := by
    unfold encodeSubst
    rw [encodeWalkstar s t1 h.1, encodeWalkstar s t2 h.1]
    rw [encodeWalkstar s2 _ h.2.1, encodeWalkstar s2 _ h.2.1, h.2.2]
  obtain ⟨result, found⟩ := tunifyAuxComplete (encodeSubst s) (encodeInferT t1)
    (encodeInferT t2) (encodeSubst s2) ⟨h.1, h.2.1, eq⟩
  have enc := encodeUnifyModelAll 0 (encodeSubst s) (encodeInferT t1) (encodeInferT t2)
    s t1 t2 ⟨rfl, Or.inl ⟨rfl, rfl⟩, h.1⟩
  rw [found] at enc
  cases hm : tUnifyModel s t1 t2 with
  | none => simp [hm] at enc
  | some sx => exact ⟨sx, rfl⟩

end Flapjack.Compiler.Inference.Unify
