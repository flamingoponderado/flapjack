module

public import Flapjack.Compiler.Inference.Unify.Occurs.Encoding
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! The inference-level substitution extension used by unification. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Proof-side form of the source extension check: encode the substitution,
    perform the first-order occurrence check and update, and decode its result.
    The occurrence model's off-well-formedness correspondence and the
    option-valued finite-map representation still need source review, so this
    definition is not tagged as the HOL declaration. -/
noncomputable def tExtSCheck (s : HolFiniteMapExact Nat InferT) (v : Nat) (t : InferT) :
    Option (HolFiniteMapExact Nat InferT) := by
  classical
  let encoded := s.map2 (fun p => encodeInferT p.2)
  exact (if Oc encoded (encodeInferT t) v then none
    else some (encoded.updateEq (v, encodeInferT t))).map
      (fun result => result.map2 (fun p => decodeInferT p.2))

/-- Decode the encoded update, including both the updated and all untouched
    entries. This is a map-encoding helper for the source extension equation. -/
theorem decodeEncodeUpdate (s : HolFiniteMapExact Nat InferT) (v : Nat)
    (t : InferT) :
    ((s.map2 (fun p => encodeInferT p.2)).updateEq (v, encodeInferT t)).map2
        (fun p => decodeInferT p.2) = s.updateEq (v, t) := by
  apply HolFiniteMapExact.ext_lookup
  intro k
  by_cases h : k = v
  · subst k
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, decodeLeftInverse.1]
  · simp only [HolFiniteMapExact.lookup_map2]
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, h]
    cases s.lookup k <;> simp [decodeLeftInverse.1]

/-- The proof-side extension reduces to the source-shaped occurrence test and
    update. The option-valued finite-map carrier remains to be reviewed before
    this is claimed as HOL's unconditional extension equation. -/
theorem tExtSCheckEqn (s : HolFiniteMapExact Nat InferT) (v : Nat) (t : InferT) :
    tExtSCheck s v t = by
      classical
      exact if tOc s t v then none else some (s.updateEq (v, t)) := by
  classical
  unfold tExtSCheck tOc
  split <;> simp_all [decodeEncodeUpdate]

end Flapjack.Compiler.Inference.Unify
