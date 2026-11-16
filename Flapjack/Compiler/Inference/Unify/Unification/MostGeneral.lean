module

public import Flapjack.Compiler.Inference.Unify.Unification.Soundness
public import Flapjack.Compiler.Inference.Unify.Walkstar.Encoding
public import Flapjack.HOL.Unification.UnifProps.MostGeneral

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Most-generality of the inference unifier model. This is untagged until
    the option-wrapped finite-map result has a reviewed HOL representation. -/
theorem tUnifyModelMostGeneral (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT)
    (sx : HolFiniteMapExact Nat InferT) (s2 : HolFiniteMapExact Nat InferT)
    (h : tWfs s ∧ tUnifyModel s t1 t2 = some sx ∧ tWfs s2 ∧
      tWalkstar s2 (tWalkstar s t1) = tWalkstar s2 (tWalkstar s t2)) :
    ∀ t, tWalkstar s2 (tWalkstar sx t) = tWalkstar s2 (tWalkstar s t) := by
  have aux := encodeUnifyModelAll 0 (encodeSubst s) (encodeInferT t1) (encodeInferT t2)
    s t1 t2 ⟨rfl, Or.inl ⟨rfl, rfl⟩, h.1⟩
  rw [h.2.1] at aux
  simp only [Option.map_some] at aux
  have eq : walkstar (encodeSubst s2) (walkstar (encodeSubst s) (encodeInferT t1)) =
      walkstar (encodeSubst s2) (walkstar (encodeSubst s) (encodeInferT t2)) := by
    unfold encodeSubst
    rw [encodeWalkstar s t1 h.1, encodeWalkstar s t2 h.1]
    rw [encodeWalkstar s2 _ h.2.2.1, encodeWalkstar s2 _ h.2.2.1, h.2.2.2]
  have result := tunifyAuxMostGeneral (encodeSubst s) (encodeInferT t1) (encodeInferT t2)
    (encodeSubst sx) (encodeSubst s2) ⟨h.1, aux, h.2.2.1, eq⟩
  have hwx := (tUnifyModelSound s t1 t2 sx ⟨h.1, h.2.1⟩).1
  intro t
  have encoded := result (encodeInferT t)
  unfold encodeSubst at encoded
  rw [encodeWalkstar sx t hwx, encodeWalkstar s t h.1,
    encodeWalkstar s2 _ h.2.2.1, encodeWalkstar s2 _ h.2.2.1] at encoded
  have decoded := congrArg decodeInferT encoded
  simpa only [decodeLeftInverse.1] using decoded

end Flapjack.Compiler.Inference.Unify
