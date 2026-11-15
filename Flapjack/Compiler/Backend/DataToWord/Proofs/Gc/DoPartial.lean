module

public import Flapjack.Compiler.Backend.WordGcFunctions

public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Selection of partial collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions

namespace doPartialMap
/-- Canonical lookup and support roundtrip for `store`. -/
theorem holFmapAsFiniteSupportParamWitness_doPartial_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad store)).lookup key = store.lookup key ∧
      (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
      FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad store) = store := ⟨rfl, rfl, rfl⟩
end doPartialMap

open Classical in
/-- Only generational configurations may select a partial collection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "do_partial_def"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
noncomputable def doPartial {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Bool :=
  match conf.gcKind with
  | .generational sizes => decide (wordGenGcCanDoPartial sizes store)
  | _ => false

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
