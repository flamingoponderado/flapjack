module

public import Flapjack.HolRef
public import Flapjack.Basis.Pure.MlString.Ops

@[expose] public section

/-!
# Cake `mlstring$fields`

Lean counterparts of `fields_aux_def` and `fields_def` in
`cakeml/basis/pure/mlstringScript.sml:621-643`: split a string at the
characters satisfying `f`, collecting the current field in reverse in `ss`.
HOL `strsub` is the tagged `Flapjack.Basis.Pure.MlString.strsub` (`EL` on the
character list), so the definitions are noncomputable like it; HOL's `string`
carrier is `List HolChar`.
-/

namespace Flapjack.Basis.Pure.MlString

open MlString

/-- Original `fields_aux_def`: walk `len` characters from position `n`, closing
the accumulated field `ss` (kept reversed) at every character satisfying `f`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_aux_def"]
noncomputable def fieldsAux (f : HolChar → Bool) (s : MlString) (ss : List HolChar)
    (n : Nat) : Nat → List MlString
  | 0 => [.implode ss.reverse]
  | len + 1 =>
      if f (strsub s n) then .implode ss.reverse :: fieldsAux f s [] (n + 1) len
      else fieldsAux f s (strsub s n :: ss) (n + 1) len

/-- Original `fields_def`: split the whole string from position `0`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_def"]
noncomputable def fields (f : HolChar → Bool) (s : MlString) : List MlString :=
  fieldsAux f s [] 0 (strlen s)

end Flapjack.Basis.Pure.MlString
