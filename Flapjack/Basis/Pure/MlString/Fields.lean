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

/-- Original `fields_alt_aux_def`: split at the separators, tracking the field
start `i` and the scan position `j`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_alt_aux_def"]
noncomputable def fieldsAltAux (f : HolChar → Bool) (s : MlString) (i j n : Nat) :
    List MlString :=
  if j < n then
    if f (strsub s j) then
      substring s i (j - i) :: fieldsAltAux f s (j + 1) (j + 1) n
    else fieldsAltAux f s i (j + 1) n
  else [substring s i (j - i)]
termination_by n - j
decreasing_by
  all_goals omega

/-- An empty substring is the empty string. -/
private theorem substring_zero_len (s : MlString) (off : Nat) :
    substring s off 0 = .implode [] := by
  simp only [substring]
  split
  · simp
  · split
    · omega
    · simp

/-- Extending the scanned prefix by one character appends that character. -/
private theorem explode_substring_succ (s : MlString) (i j : Nat) (hij : i ≤ j)
    (hjn : j < strlen s) :
    explode (substring s i (j + 1 - i)) =
      explode (substring s i (j - i)) ++ [strsub s j] := by
  have hstep : j + 1 - i = (j - i) + 1 := by omega
  have hbound : i + (j - i) + 1 ≤ strlen s := by omega
  have hij' : i + (j - i) = j := by omega
  rw [hstep, substring_add s i (j - i) 1 hbound, hij', substring_one_strsub s j hjn]
  simp only [explode_strcat, explode_implode_eq, chrToStr]

/-- Original `fields_alt_fields_alt_aux`: the scan-based splitter agrees with
`fields_aux` at every starting point. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_alt_fields_alt_aux"]
theorem fieldsAlt_fieldsAux (f : HolChar → Bool) (s : MlString) :
    ∀ (l : Nat) (acc : List HolChar) (j i : Nat), i ≤ j → j ≤ strlen s →
      strlen s - j = l → acc = (explode (substring s i (j - i))).reverse →
      fieldsAux f s acc j l = fieldsAltAux f s i j (strlen s) := by
  intro l
  induction l with
  | zero =>
      intro acc j i hij hjn hlen hacc
      have hjeq : j = strlen s := by omega
      subst j
      rw [fieldsAux, fieldsAltAux.eq_def, if_neg (by omega : ¬ strlen s < strlen s)]
      rw [hacc, List.reverse_reverse, implode_explode]
  | succ l ih =>
      intro acc j i hij hjn hlen hacc
      have hjn' : j < strlen s := by omega
      have hnext : strlen s - (j + 1) = l := by omega
      rw [fieldsAux, fieldsAltAux.eq_def, if_pos hjn']
      by_cases hf : f (strsub s j)
      · rw [if_pos hf, if_pos hf]
        have hhead : .implode acc.reverse = substring s i (j - i) := by
          rw [hacc, List.reverse_reverse, implode_explode]
        have htail :
            fieldsAux f s [] (j + 1) l = fieldsAltAux f s (j + 1) (j + 1) (strlen s) := by
          refine ih [] (j + 1) (j + 1) (by omega) (by omega) hnext ?_
          rw [Nat.sub_self]
          simp only [substring_zero_len, explode_implode_eq, List.reverse_nil]
        rw [hhead, htail]
      · rw [if_neg hf, if_neg hf]
        have hacc' :
            strsub s j :: acc = (explode (substring s i (j + 1 - i))).reverse := by
          rw [hacc, explode_substring_succ s i j hij hjn', List.reverse_append]
          rw [List.reverse_singleton]
          rfl
        exact ih (strsub s j :: acc) (j + 1) i (by omega) (by omega) hnext hacc'

/-- Original `fields_alt`: splitting the whole string from position `0`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fields_alt"]
theorem fields_alt (f : HolChar → Bool) (s : MlString) :
    fields f s = fieldsAltAux f s 0 0 (strlen s) := by
  rw [fields]
  exact fieldsAlt_fieldsAux f s (strlen s) [] 0 0 (by omega) (by omega) (by omega) (by simp)

/-- Flapjack infrastructure: the field walk always returns at least one field. -/
private theorem fieldsAux_ne_nil (f : HolChar → Bool) (s : MlString) :
    ∀ (ss : List HolChar) (n len : Nat), fieldsAux f s ss n len ≠ [] := by
  intro ss n len
  induction len generalizing ss n with
  | zero => simp [fieldsAux]
  | succ len ih =>
    rw [fieldsAux]
    split
    · simp
    · exact ih _ _

/-- Original `FIELDS_NEQ_NIL`: splitting a string into fields never returns the
empty list. -/
@[hol "cakeml/misc/miscScript.sml" "FIELDS_NEQ_NIL"]
theorem fields_ne_nil (P : HolChar → Bool) (ls : MlString) : fields P ls ≠ [] := by
  unfold fields
  exact fieldsAux_ne_nil P ls [] 0 (strlen ls)

end Flapjack.Basis.Pure.MlString
