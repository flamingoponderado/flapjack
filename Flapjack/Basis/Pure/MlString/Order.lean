module

public import Flapjack.Basis.Pure.MlString.Ops
public import Flapjack.Basis.Pure.MlList.Collate

@[expose] public section

/-!
# Cake `mlstring` ordering

Lean counterparts of `compare_aux_def`, `compare_def`, `mlstring_lt_def`,
`mlstring_le_def`, `mlstring_gt_def`, `mlstring_ge_def`, `fast_lt_def`,
`fast_le_def`, `fast_gt_def`, `fast_ge_def`, `collate_aux_def` and
`collate_def` in `cakeml/basis/pure/mlstringScript.sml`.

HOL's `ordering` is Lean's `Ordering`, so `Less`, `Equal` and `Greater` are
`.lt`, `.eq` and `.gt`; HOL `char_lt` is the unsigned byte order on
`HolChar = BitVec 8`; and `strsub` and `strlen` are the tagged renderings, which
makes the definitions noncomputable. The four ordering predicates are
bool-valued in HOL, so they are `decide` of the corresponding `Ordering`
comparison.
-/

namespace Flapjack.Basis.Pure.MlString.Order

open Flapjack.Basis.Pure.MlString.MlString

/-- Original `compare_aux_def`: compare `len` characters starting at `start`,
    keeping `ord` while they are equal. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "compare_aux_def"]
noncomputable def compareAux (s1 s2 : MlString) (ord : Ordering) (start len : Nat) : Ordering :=
  if len = 0 then ord
  else if strsub s2 start < strsub s1 start then .gt
  else if strsub s1 start < strsub s2 start then .lt
  else compareAux s1 s2 ord (start + 1) (len - 1)
termination_by len

/-- Original `compare_def`: the shorter string is smaller, and otherwise the
    common prefix decides. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "compare_def"]
noncomputable def compare (s1 s2 : MlString) : Ordering :=
  if strlen s1 < strlen s2 then compareAux s1 s2 .lt 0 (strlen s1)
  else if strlen s2 < strlen s1 then compareAux s1 s2 .gt 0 (strlen s2)
  else compareAux s1 s2 .eq 0 (strlen s2)

/-- Original `mlstring_lt_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_def"]
noncomputable def mlstringLt (s1 s2 : MlString) : Bool := decide (compare s1 s2 = .lt)

/-- Original `mlstring_le_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_le_def"]
noncomputable def mlstringLe (s1 s2 : MlString) : Bool := decide (compare s1 s2 ≠ .gt)

/-- Original `mlstring_gt_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_gt_def"]
noncomputable def mlstringGt (s1 s2 : MlString) : Bool := decide (compare s1 s2 = .gt)

/-- Original `mlstring_ge_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_ge_def"]
noncomputable def mlstringGe (s1 s2 : MlString) : Bool := decide (compare s1 s2 ≠ .lt)

/-- Original `fast_lt_def`: order by length first, then by the common prefix. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_lt_def"]
noncomputable def fastLt (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringLt s1 s2 else decide (strlen s1 < strlen s2)

/-- Original `fast_le_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_le_def"]
noncomputable def fastLe (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringLe s1 s2 else decide (strlen s1 ≤ strlen s2)

/-- Original `fast_gt_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_gt_def"]
noncomputable def fastGt (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringGt s1 s2 else decide (strlen s1 > strlen s2)

/-- Original `fast_ge_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "fast_ge_def"]
noncomputable def fastGe (s1 s2 : MlString) : Bool :=
  if strlen s1 = strlen s2 then mlstringGe s1 s2 else decide (strlen s1 ≥ strlen s2)

/-- Original `collate_aux_def`: compare `len` characters with the given
    character comparison, keeping `ord` while it reports `Equal`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "collate_aux_def"]
noncomputable def collateAux (f : HolChar → HolChar → Ordering) (s1 s2 : MlString)
    (ord : Ordering) (n : Nat) : Nat → Ordering
  | 0 => ord
  | len + 1 =>
    if f (strsub s1 n) (strsub s2 n) = .eq then collateAux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n)

/-- Original `collate_def`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "collate_def"]
noncomputable def collate (f : HolChar → HolChar → Ordering) (s1 s2 : MlString) : Ordering :=
  if strlen s1 < strlen s2 then collateAux f s1 s2 .lt 0 (strlen s1)
  else if strlen s2 < strlen s1 then collateAux f s1 s2 .gt 0 (strlen s2)
  else collateAux f s1 s2 .eq 0 (strlen s2)

/-- Original `compare_thm`: the ordering predicates describe `compare`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "compare_thm"]
theorem compare_thm (s1 s2 : MlString) :
    compare s1 s2 =
      if mlstringLt s1 s2 then .lt else if mlstringLe s1 s2 then .eq else .gt := by
  unfold mlstringLt mlstringLe
  cases compare s1 s2
  · simp
  · simp
  · simp

/-- Original `collate_aux_less_thm[local]`: the shorter-string scan is the
lexicographic comparison of the suffixes. -/
private theorem collateAux_lt (f : HolChar → HolChar → Ordering) (s1 s2 : MlString) :
    ∀ (n len : Nat), n + len = strlen s1 → strlen s1 < strlen s2 →
      collateAux f s1 s2 .lt n len =
        Flapjack.Basis.Pure.MlList.collate f ((explode s1).drop n) ((explode s2).drop n) := by
  intro n len
  revert n
  induction len with
  | zero =>
    intro n hn hlt
    have hn' : n = strlen s1 := by omega
    subst n
    have hstr : strlen s1 = (explode s1).length := strlen_eq_explode_length s1
    have hstr2 : strlen s2 = (explode s2).length := strlen_eq_explode_length s2
    have hle : (explode s1).length ≤ strlen s1 := by
      rw [strlen_eq_explode_length]
      omega
    have h1 : (explode s1).drop (strlen s1) = [] := List.drop_eq_nil_of_le hle
    rw [collateAux, h1]
    have hne : (explode s2).drop (strlen s1) ≠ [] := by
      intro hnil
      rw [List.drop_eq_nil_iff] at hnil
      omega
    cases hdrop : (explode s2).drop (strlen s1) with
    | nil => exact absurd hdrop hne
    | cons h t => rfl
  | succ len ih =>
    intro n hn hlt
    have hnlt : n < strlen s1 := by omega
    have hn2 : n < strlen s2 := by omega
    have hnext : n + 1 + len = strlen s1 := by omega
    have hi1 : n < (explode s1).length := by
      rw [strlen_eq_explode_length] at hnlt
      exact hnlt
    have hi2 : n < (explode s2).length := by
      rw [strlen_eq_explode_length] at hn2
      exact hn2
    have hsub1 : strsub s1 n = (explode s1)[n] := holEl_eq_getElem n (explode s1) hi1
    have hsub2 : strsub s2 n = (explode s2)[n] := holEl_eq_getElem n (explode s2) hi2
    rw [collateAux, hsub1, hsub2, List.drop_eq_getElem_cons hi1, List.drop_eq_getElem_cons hi2]
    by_cases heq : f (explode s1)[n] (explode s2)[n] = .eq
    · rw [if_pos heq, ih (n + 1) hnext hlt, Flapjack.Basis.Pure.MlList.collate, if_pos heq]
    · rw [if_neg heq, Flapjack.Basis.Pure.MlList.collate, if_neg heq]

/-- Original `collate_aux_equal_thm[local]`: the equal-length scan is the
lexicographic comparison of the suffixes. -/
private theorem collateAux_eq (f : HolChar → HolChar → Ordering) (s1 s2 : MlString) :
    ∀ (n len : Nat), n + len = strlen s2 → strlen s1 = strlen s2 →
      collateAux f s1 s2 .eq n len =
        Flapjack.Basis.Pure.MlList.collate f ((explode s1).drop n) ((explode s2).drop n) := by
  intro n len
  revert n
  induction len with
  | zero =>
    intro n hn heq
    have hn' : n = strlen s2 := by omega
    subst n
    have hlen_eq : (explode s1).length = (explode s2).length := by
      rw [← strlen_eq_explode_length, ← strlen_eq_explode_length]
      exact heq
    have hstr2 : strlen s2 = (explode s2).length := strlen_eq_explode_length s2
    have hle : (explode s1).length ≤ strlen s2 := by
      rw [strlen_eq_explode_length]
      omega
    have h1 : (explode s1).drop (strlen s2) = [] := List.drop_eq_nil_of_le hle
    have hle2 : (explode s2).length ≤ strlen s2 := by
      rw [strlen_eq_explode_length]
      omega
    have h2 : (explode s2).drop (strlen s2) = [] := List.drop_eq_nil_of_le hle2
    rw [collateAux, h1, h2]
    rfl
  | succ len ih =>
    intro n hn heq
    have hn2 : n < strlen s2 := by omega
    have hn1 : n < strlen s1 := by omega
    have hnext : n + 1 + len = strlen s2 := by omega
    have hi1 : n < (explode s1).length := by
      rw [strlen_eq_explode_length] at hn1
      exact hn1
    have hi2 : n < (explode s2).length := by
      rw [strlen_eq_explode_length] at hn2
      exact hn2
    have hsub1 : strsub s1 n = (explode s1)[n] := holEl_eq_getElem n (explode s1) hi1
    have hsub2 : strsub s2 n = (explode s2)[n] := holEl_eq_getElem n (explode s2) hi2
    rw [collateAux, hsub1, hsub2, List.drop_eq_getElem_cons hi1, List.drop_eq_getElem_cons hi2]
    by_cases hf : f (explode s1)[n] (explode s2)[n] = .eq
    · rw [if_pos hf, ih (n + 1) hnext heq, Flapjack.Basis.Pure.MlList.collate, if_pos hf]
    · rw [if_neg hf, Flapjack.Basis.Pure.MlList.collate, if_neg hf]

/-- Original `collate_aux_greater_thm[local]`: the longer-string scan is the
lexicographic comparison of the suffixes. -/
private theorem collateAux_gt (f : HolChar → HolChar → Ordering) (s1 s2 : MlString) :
    ∀ (n len : Nat), n + len = strlen s2 → strlen s2 < strlen s1 →
      collateAux f s1 s2 .gt n len =
        Flapjack.Basis.Pure.MlList.collate f ((explode s1).drop n) ((explode s2).drop n) := by
  intro n len
  revert n
  induction len with
  | zero =>
    intro n hn hlt
    have hn' : n = strlen s2 := by omega
    subst n
    have hstr : strlen s2 = (explode s2).length := strlen_eq_explode_length s2
    have hstr1 : strlen s1 = (explode s1).length := strlen_eq_explode_length s1
    have hle2 : (explode s2).length ≤ strlen s2 := by
      rw [strlen_eq_explode_length]
      omega
    have h2 : (explode s2).drop (strlen s2) = [] := List.drop_eq_nil_of_le hle2
    rw [collateAux, h2]
    have hne : (explode s1).drop (strlen s2) ≠ [] := by
      intro hnil
      rw [List.drop_eq_nil_iff] at hnil
      omega
    cases hdrop : (explode s1).drop (strlen s2) with
    | nil => exact absurd hdrop hne
    | cons h t => rfl
  | succ len ih =>
    intro n hn hlt
    have hn2 : n < strlen s2 := by omega
    have hn1 : n < strlen s1 := by omega
    have hnext : n + 1 + len = strlen s2 := by omega
    have hi1 : n < (explode s1).length := by
      rw [strlen_eq_explode_length] at hn1
      exact hn1
    have hi2 : n < (explode s2).length := by
      rw [strlen_eq_explode_length] at hn2
      exact hn2
    have hsub1 : strsub s1 n = (explode s1)[n] := holEl_eq_getElem n (explode s1) hi1
    have hsub2 : strsub s2 n = (explode s2)[n] := holEl_eq_getElem n (explode s2) hi2
    rw [collateAux, hsub1, hsub2, List.drop_eq_getElem_cons hi1, List.drop_eq_getElem_cons hi2]
    by_cases hf : f (explode s1)[n] (explode s2)[n] = .eq
    · rw [if_pos hf, ih (n + 1) hnext hlt, Flapjack.Basis.Pure.MlList.collate, if_pos hf]
    · rw [if_neg hf, Flapjack.Basis.Pure.MlList.collate, if_neg hf]

/-- Original `collate_thm`: the string scan agrees with the list comparison. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "collate_thm"]
theorem collate_thm (f : HolChar → HolChar → Ordering) (s1 s2 : MlString) :
    collate f s1 s2 =
      Flapjack.Basis.Pure.MlList.collate f (explode s1) (explode s2) := by
  rw [collate]
  by_cases hlt : strlen s1 < strlen s2
  · rw [if_pos hlt, collateAux_lt f s1 s2 0 (strlen s1) (by omega) hlt]
    simp only [List.drop_zero]
  · rw [if_neg hlt]
    by_cases hgt : strlen s2 < strlen s1
    · rw [if_pos hgt, collateAux_gt f s1 s2 0 (strlen s2) (by omega) hgt]
      simp only [List.drop_zero]
    · rw [if_neg hgt, collateAux_eq f s1 s2 0 (strlen s2) (by omega) (by omega)]
      simp only [List.drop_zero]

end Flapjack.Basis.Pure.MlString.Order
