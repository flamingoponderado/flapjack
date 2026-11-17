module

public import Flapjack.Compiler.Inference.Unify.Compat
public import Flapjack.Compiler.Inference.Unify.Unification.Complete

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify

/-- Compatibility of a successful inference-unifier model result with any
    compatible solution. This remains untagged until the source unifier and
    its option-wrapped finite-map result have reviewed correspondence. -/
theorem tCompatUnifyModelComplete (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT)
    (sx : HolFiniteMapExact Nat InferT)
    (h : tCompat s sx ∧ tWalkstar sx t1 = tWalkstar sx t2) :
    ∃ si, tUnifyModel s t1 t2 = some si ∧ tCompat si sx := by
  have equal : tWalkstar sx (tWalkstar s t1) = tWalkstar sx (tWalkstar s t2) := by
    rw [h.1.2.2 t1, h.1.2.2 t2, h.2]
  obtain ⟨si, found⟩ := tUnifyModelComplete s t1 t2 sx ⟨h.1.1, h.1.2.1, equal⟩
  refine ⟨si, found, (tUnifyModelSound s t1 t2 si ⟨h.1.1, found⟩).1, h.1.2.1, ?_⟩
  intro t
  rw [tUnifyModelMostGeneral s t1 t2 si sx ⟨h.1.1, found, h.1.2.1, equal⟩ t,
    h.1.2.2 t]

end Flapjack.Compiler.Inference.Unify
