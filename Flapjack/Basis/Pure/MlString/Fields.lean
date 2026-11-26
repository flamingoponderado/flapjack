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

/-- Concatenating the fields drops the separator characters. -/
private theorem fieldsAux_concat (f : HolChar → Bool) (s : MlString) :
    ∀ (ss : List HolChar) (len n : Nat), n + len = strlen s →
      concat (fieldsAux f s ss n len) =
        .implode (ss.reverse ++ ((explode s).drop n).filter (fun c => !(f c))) := by
  intro ss len n
  revert ss n
  induction len with
  | zero =>
    intro ss n h
    have hn : (explode s).length ≤ n := by
      simp only [strlen_eq_explode_length] at h
      omega
    simp only [fieldsAux, List.drop_eq_nil_of_le hn, List.filter_nil, List.append_nil]
    simp only [concat_cons, concat_nil, strcat_nil]
  | succ len ih =>
    intro ss n h
    have hn : n < (explode s).length := by
      simp only [strlen_eq_explode_length] at h
      omega
    have hnext : n + 1 + len = strlen s := by omega
    have hsub : strsub s n = (explode s)[n] := holEl_eq_getElem n (explode s) hn
    simp only [fieldsAux, hsub, List.drop_eq_getElem_cons hn]
    by_cases hf : f (explode s)[n]
    · simp only [hf, if_true, List.filter_cons, concat_cons]
      rw [strcat_eq_implode_append, explode_implode, explode_implode, ih [] (n + 1) hnext]
      simp
    · simp only [hf, Bool.false_eq_true, if_false, List.filter_cons,
        ih ((explode s)[n] :: ss) (n + 1) hnext]
      simp

/-- The number of fields is one more than the separators. -/
private theorem fieldsAux_length (f : HolChar → Bool) (s : MlString) :
    ∀ (ss : List HolChar) (len n : Nat), n + len = strlen s →
      (fieldsAux f s ss n len).length =
        (((explode s).drop n).filter (fun c => f c)).length + 1 := by
  intro ss len n
  revert ss n
  induction len with
  | zero =>
    intro ss n h
    have hn : (explode s).length ≤ n := by
      simp only [strlen_eq_explode_length] at h
      omega
    simp only [fieldsAux, List.drop_eq_nil_of_le hn, List.filter_nil, List.length_cons,
      List.length_nil]
  | succ len ih =>
    intro ss n h
    have hn : n < (explode s).length := by
      simp only [strlen_eq_explode_length] at h
      omega
    have hnext : n + 1 + len = strlen s := by omega
    have hsub : strsub s n = (explode s)[n] := holEl_eq_getElem n (explode s) hn
    simp only [fieldsAux, hsub, List.drop_eq_getElem_cons hn]
    by_cases hf : f (explode s)[n]
    · simp only [hf, if_true, List.length_cons, List.filter_cons]
      rw [ih [] (n + 1) hnext]
    · simp only [hf, Bool.false_eq_true, if_false, List.filter_cons]
      rw [ih ((explode s)[n] :: ss) (n + 1) hnext]

/-- Original `fields_filter`: concatenating the fields drops the separators. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_filter"]
theorem fields_concat (f : HolChar → Bool) (s : MlString) :
    concat (fields f s) = .implode (((explode s).filter (fun c => !(f c)))) := by
  unfold fields
  simpa using fieldsAux_concat f s [] (strlen s) 0 (by omega)

/-- Original `fields_length`: one field more than there are separators. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_length"]
theorem fields_length (f : HolChar → Bool) (s : MlString) :
    (fields f s).length = (((explode s).filter (fun c => f c)).length + 1) := by
  unfold fields
  simpa using fieldsAux_length f s [] (strlen s) 0 (by omega)

end Flapjack.Basis.Pure.MlString
