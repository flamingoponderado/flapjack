module

public import Flapjack.HolRef
public import Flapjack.Basis.Pure.MlString.Ops

@[expose] public section

/-!
# Cake `mlstring` prefix, suffix and substring tests

Lean counterparts of `isStringThere_aux_def`, `isPrefix_def`, `isSuffix_def`,
`isSubstring_aux_def` and `isSubstring_def` in
`cakeml/basis/pure/mlstringScript.sml:762-855`: `isStringThere_aux` compares a
fixed number of characters from two positions, and the three tests scan for a
prefix, a suffix or any occurrence. HOL `strsub` and `strlen` are the tagged
renderings in `Flapjack.Basis.Pure.MlString.Ops`, so the definitions are
noncomputable like `strsub`; HOL's `string` carrier is `List HolChar`.
-/

namespace Flapjack.Basis.Pure.MlString

open MlString

/-- Original `isStringThere_aux_def`: compare `len` characters starting at
positions `s1i` and `s2i`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isStringThere_aux_def"]
noncomputable def isStringThereAux (s1 s2 : MlString) (s1i s2i : Nat) : Nat → Bool
  | 0 => true
  | len + 1 =>
      if strsub s1 s1i = strsub s2 s2i then isStringThereAux s1 s2 (s1i + 1) (s2i + 1) len
      else false

/-- Original `isPrefix_def`: `s1` occurs at the start of `s2`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isPrefix_def"]
noncomputable def isPrefix (s1 s2 : MlString) : Bool :=
  if strlen s1 ≤ strlen s2 then isStringThereAux s1 s2 0 0 (strlen s1) else false

/-- Original `isSuffix_def`: `s1` occurs at the end of `s2`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isSuffix_def"]
noncomputable def isSuffix (s1 s2 : MlString) : Bool :=
  if strlen s1 ≤ strlen s2 then isStringThereAux s1 s2 0 (strlen s2 - strlen s1) (strlen s1)
  else false

/-- Original `isSubstring_aux_def`: try the `len` start positions from `n`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isSubstring_aux_def"]
noncomputable def isSubstringAux (s1 s2 : MlString) (lens1 n : Nat) : Nat → Bool
  | 0 => false
  | len + 1 =>
      if isStringThereAux s1 s2 0 n lens1 then true
      else isSubstringAux s1 s2 lens1 (n + 1) len

/-- Original `isSubstring_def`: `s1` occurs anywhere in `s2`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isSubstring_def"]
noncomputable def isSubstring (s1 s2 : MlString) : Bool :=
  if strlen s1 ≤ strlen s2 then
    isSubstringAux s1 s2 (strlen s1) 0 (strlen s2 - strlen s1 + 1)
  else false

end Flapjack.Basis.Pure.MlString
