import Flapjack.Compiler.Backend.FlatPattern.Proofs.DecisionEncoding.Encoding
import Flapjack.Misc.ListEl

namespace Flapjack.Compiler.Backend.FlatPattern

open Flapjack Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (StoreValue storeLookup)

/-- The original lookup equation for the encoded finite reference map. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "FLOOKUP_encode_refs"
  (fmap_as_finite_support_result_observations := [encodeRefs])]
theorem flookup_encodeRefs {C F : Type} (state : FlatSem.State C F) (index : Nat) :
    (encodeRefs state).lookup index =
      if index < state.refs.length then
        match @Flapjack.holEl (StoreValue FlatSem.Value) ⟨.w8array []⟩ index state.refs with
        | .refv value => some (encodeValue value)
        | _ => none
      else none := by
  let : Nonempty (StoreValue FlatSem.Value) := ⟨.w8array []⟩
  by_cases bound : index < state.refs.length
  · simp only [encodeRefs, storeLookup, bound, ↓reduceIte, List.getElem?_eq_getElem bound,
      Flapjack.holEl_eq_getElem index state.refs bound]
    cases state.refs[index]'bound <;> rfl
  · simp [encodeRefs, storeLookup, bound]

end Flapjack.Compiler.Backend.FlatPattern
