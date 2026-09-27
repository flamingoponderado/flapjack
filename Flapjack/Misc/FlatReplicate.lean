import Flapjack.HolRef

/-!
# HOL `misc$FLAT_REPLICATE_NIL`

Counterpart of `FLAT_REPLICATE_NIL` from `cakeml/misc/miscScript.sml:2120`:
`!n. FLAT (REPLICATE n []) = []`, i.e. flattening a list of `n` empty lists is
empty.  HOL `FLAT` is rendered as Lean `List.flatten` and HOL `REPLICATE` as
Lean `List.replicate`; the list element type stays an implicit parameter, as in
HOL.
-/

namespace Flapjack

/-- Exact port of HOL `FLAT_REPLICATE_NIL`
(`cakeml/misc/miscScript.sml:2120`): `!n. FLAT (REPLICATE n []) = []`. -/
@[hol "cakeml/misc/miscScript.sml" "FLAT_REPLICATE_NIL"]
theorem flatReplicateNilHOL {α : Type} (n : Nat) :
    (List.replicate n ([] : List α)).flatten = [] := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, ih]

end Flapjack
