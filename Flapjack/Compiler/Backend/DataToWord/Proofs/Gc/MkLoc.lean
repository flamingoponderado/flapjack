module

public import Flapjack.Compiler.Backend.Semantics.WordSem.State

@[expose] public section

/-! Exception-location selector used by data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.loc 0 0⟩

/-- The fixed but unspecified result of HOL's `mk_loc NONE`, indexed by both
independent source type parameters. No equality with another unspecified HOL
value is assumed. -/
noncomputable opaque mkLocNone (width : Nat) [NeZero width] (payload : Type) : WordLocW width

/-- The source equation specifies the location only when the input is `SOME`.
HOL's discarded payload type is independent of the result word dimension. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "mk_loc_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mkLoc {width : Nat} [NeZero width] {payload : Type} :
    Option (payload × Nat × Nat) → WordLocW width
  | some (_, l1, l2) => .loc l1 l2
  | none => mkLocNone width payload

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
