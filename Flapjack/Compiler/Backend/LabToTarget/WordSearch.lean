import Flapjack.Misc.FindIndex
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Misc

/-- Full original local word-search transport. The optional result, arbitrary offset and duplicates remain;
only injectivity of the reviewed word-to-natural projection is needed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "find_index_MAP_w2n" (words_as_type_indexed_bitvec)]
theorem findIndex_mapToNat {width : Nat} [NeZero width]
    (values : List (BitVec width)) (target : BitVec width) (offset : Nat) :
    findIndex target.toNat (values.map BitVec.toNat) offset =
      findIndex target values offset := by
  induction values generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    have he : head.toNat = target.toNat ↔ head = target := BitVec.toNat_inj
    simp only [List.map_cons,findIndex,he]
    split
    · rfl
    · exact ih (offset+1)
end Flapjack.Compiler.Backend.LabToTarget
