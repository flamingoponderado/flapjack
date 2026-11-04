import Flapjack.Compiler.Backend.WordGcFunctions

/-! Selection of partial collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions

open Classical in
/-- Only generational configurations may select a partial collection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "do_partial_def"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
noncomputable def doPartial {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Bool :=
  match conf.gcKind with
  | .generational sizes => decide (wordGenGcCanDoPartial sizes store)
  | _ => false

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
