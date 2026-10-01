import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.CodeLabels
import Mathlib.Data.Set.Lattice

namespace Flapjack

/-- Literal whole-program source code-label safety. The original EVERY owner
handler guard and full source label union are retained; external labels are an
arbitrary HOL-shaped set, with no finiteness or distinct-key requirement. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "good_code_labels_def" (words_as_type_indexed_bitvec)]
def goodCodeLabelsHOL {width : Nat} [NeZero width]
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (externalLabels : Set Nat) : Prop :=
  rows.all (fun row => goodHandlersHOL row.1 row.2.2) = true ∧
    Set.sUnion {labels | labels ∈ rows.map (fun row => getCodeLabelsHOL row.2.2)} ⊆
      {name | name ∈ rows.map Prod.fst} ∪ externalLabels

end Flapjack
