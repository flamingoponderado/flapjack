import Flapjack.Compiler.Backend.LabToTarget.LabelLookup
import Flapjack.Pancake.WordLang

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack

/-- Literal register-value conversion used by the original full state relation.
Words are unchanged; locations require successful lookup in the actual nested
label tree and use modular base-plus-offset word arithmetic. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "word_loc_val_def" (words_as_type_indexed_bitvec)]
def wordLocVal {width : Nat} [NeZero width] (p : BitVec width)
    (labs : Spt (Spt Nat)) : WordLocW width → Option (BitVec width)
  | .word w => some w
  | .loc k1 k2 =>
      match labLookup k1 k2 labs with
      | none => none
      | some q => some (p + BitVec.ofNat width q)

end Flapjack.Compiler.Backend.LabToTarget
