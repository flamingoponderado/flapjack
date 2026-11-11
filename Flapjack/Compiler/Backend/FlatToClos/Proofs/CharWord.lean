module

public import Flapjack.Basis.Pure.MlString.CharWord

@[expose] public section

namespace Flapjack.Compiler.Backend.FlatToClos

open Flapjack.Basis.Pure.MlString

/-- Mapping HOL `n2w ∘ ORD` to byte words is injective on character lists. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "MAP_n2w_o_ORD_11"]
theorem mapN2wOrd_injective (l1 l2 : List HolChar) :
    l1.map (BitVec.ofNat 8 ∘ BitVec.toNat) = l2.map (BitVec.ofNat 8 ∘ BitVec.toNat) ↔
      l1 = l2 := by
  simp [Function.comp_def]

/-- The second local HOL formulation uses the same character-to-byte map. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "MAP_n2w_ORD_eq"]
theorem mapN2wOrd_eq (s s' : List HolChar) :
    s.map (BitVec.ofNat 8 ∘ BitVec.toNat) = s'.map (BitVec.ofNat 8 ∘ BitVec.toNat) ↔
      s = s' :=
  mapN2wOrd_injective s s'

end Flapjack.Compiler.Backend.FlatToClos
