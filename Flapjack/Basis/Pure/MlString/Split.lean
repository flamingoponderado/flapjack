module

public import Flapjack.HolRef
public import Flapjack.Basis.Pure.MlString.Ops

@[expose] public section

/-!
# Cake `mlstring$splitl` and `mlstring$tokens`

Lean counterparts of `splitl_aux_def`, `splitl_def`, `tokens_aux_def` and
`tokens_def` in `cakeml/basis/pure/mlstringScript.sml`, together with
`tokens_filter`.  HOL's `string` carrier is `List HolChar`, `strsub` is the
tagged `Flapjack.Basis.Pure.MlString.strsub` (`EL` on the character list) and
`extract` is the tagged `extract`, so the definitions are noncomputable like
them.  HOL's boolean conjunction in the `splitl_aux` guard is Lean's `&&`.
-/

namespace Flapjack.Basis.Pure.MlString

open MlString

/-- Original `splitl_aux_def`: consume characters while `P` holds, returning the
consumed prefix and the remaining suffix. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "splitl_aux_def"]
noncomputable def splitlAux (P : HolChar → Bool) (s : MlString) (i : Nat) :
    MlString × MlString :=
  if i < strlen s && P (strsub s i) then splitlAux P s (i + 1)
  else (extract s 0 (some i), extract s i none)
termination_by strlen s - i
decreasing_by
  simp_all only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Original `splitl_def`: split from the first character. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "splitl_def"]
noncomputable def splitl (P : HolChar → Bool) (s : MlString) : MlString × MlString :=
  splitlAux P s 0

/-- Original `tokens_aux_def`: collect the maximal runs of characters that do
not satisfy `f`, keeping the current run reversed in `ss`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "tokens_aux_def"]
noncomputable def tokensAux (f : HolChar → Bool) (s : MlString) (ss : List HolChar)
    (n : Nat) : Nat → List MlString
  | 0 => match ss with
      | [] => []
      | h :: t => [.implode (h :: t).reverse]
  | len + 1 => match ss with
      | [] =>
        if f (strsub s n) then tokensAux f s [] (n + 1) len
        else tokensAux f s [strsub s n] (n + 1) len
      | h :: t =>
        if f (strsub s n) then
          .implode (h :: t).reverse :: tokensAux f s [] (n + 1) len
        else tokensAux f s (strsub s n :: h :: t) (n + 1) len

/-- Original `tokens_def`: split the whole string at the characters satisfying
`f`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "tokens_def"]
noncomputable def tokens (f : HolChar → Bool) (s : MlString) : List MlString :=
  tokensAux f s [] 0 (strlen s)

/-- Concatenating the tokens drops the separator characters. -/
private theorem tokensAux_concat (f : HolChar → Bool) (s : MlString) :
    ∀ (ss : List HolChar) (len n : Nat), n + len = strlen s →
      concat (tokensAux f s ss n len) =
        .implode (ss.reverse ++ ((explode s).drop n).filter (fun c => !(f c))) := by
  intro ss len n
  revert ss n
  induction len with
  | zero =>
    intro ss n h
    have hn : (explode s).length ≤ n := by
      simp only [strlen_eq_explode_length] at h
      omega
    cases ss with
    | nil =>
      simp only [tokensAux, List.drop_eq_nil_of_le hn, List.filter_nil, List.append_nil,
        List.reverse_nil, concat_nil]
    | cons h t =>
      simp only [tokensAux, List.drop_eq_nil_of_le hn, List.filter_nil, List.append_nil,
        concat_cons, concat_nil, strcat_eq_implode_append, explode_implode]
  | succ len ih =>
    intro ss n h
    have hn : n < (explode s).length := by
      simp only [strlen_eq_explode_length] at h
      omega
    have hnext : n + 1 + len = strlen s := by omega
    have hsub : strsub s n = (explode s)[n] := holEl_eq_getElem n (explode s) hn
    simp only [tokensAux, hsub, List.drop_eq_getElem_cons hn]
    by_cases hf : f (explode s)[n]
    · cases ss with
      | nil =>
        simp only [hf, if_true, List.filter_cons]
        rw [ih [] (n + 1) hnext]
        simp
      | cons h t =>
        simp only [hf, if_true, List.filter_cons, concat_cons]
        rw [strcat_eq_implode_append, explode_implode, ih [] (n + 1) hnext]
        simp
    · cases ss with
      | nil =>
        simp only [hf, Bool.false_eq_true, if_false, List.filter_cons,
          ih [(explode s)[n]] (n + 1) hnext]
        simp
      | cons h t =>
        simp only [hf, Bool.false_eq_true, if_false, List.filter_cons,
          ih ((explode s)[n] :: h :: t) (n + 1) hnext]
        simp

/-- Original `tokens_filter`: concatenating the tokens drops the separators. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "tokens_filter"]
theorem tokens_concat (f : HolChar → Bool) (s : MlString) :
    concat (tokens f s) = .implode ((explode s).filter (fun c => !(f c))) := by
  unfold tokens
  simpa using tokensAux_concat f s [] (strlen s) 0 (by omega)

/-- Original `tokens_alt_aux_def`: collect the maximal runs of non-separator
characters while tracking the run start `i` and the scan position `j`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "tokens_alt_aux_def"]
noncomputable def tokensAltAux (f : HolChar → Bool) (s : MlString) (i j n : Nat) :
    List MlString :=
  if j < n then
    if f (strsub s j) then
      if i = j then tokensAltAux f s (i + 1) (j + 1) n
      else substring s i (j - i) :: tokensAltAux f s (j + 1) (j + 1) n
    else tokensAltAux f s i (j + 1) n
  else if i = j then [] else [substring s i (j - i)]
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

/-- The reversed prefix is empty exactly when the run start reached the scan
position. -/
private theorem acc_nil_iff (s : MlString) (i j : Nat) (hij : i ≤ j) (hjn : j ≤ strlen s) :
    (explode (substring s i (j - i))).reverse = [] ↔ i = j := by
  have hbound : i + (j - i) ≤ strlen s := by omega
  have hlen : strlen (substring s i (j - i)) = j - i := by
    rw [strlen_substring, if_pos hbound]
  constructor
  · intro h
    have h0 : (explode (substring s i (j - i))).length = 0 := by
      have := congrArg List.length h
      simpa using this
    rw [← strlen_eq_explode_length, hlen] at h0
    omega
  · intro h
    have h0 : j - i = 0 := by omega
    have hlen0 : (explode (substring s i (j - i))).length = 0 := by
      rw [← strlen_eq_explode_length, hlen, h0]
    have hnil : explode (substring s i (j - i)) = [] := List.eq_nil_of_length_eq_zero hlen0
    rw [hnil]
    rfl

/-- A one-character prefix starting at `j` is that character. -/
private theorem singleton_eq_reverse_substring (s : MlString) (j : Nat) (hjn : j < strlen s) :
    [strsub s j] = (explode (substring s j (j + 1 - j))).reverse := by
  have h1 : j + 1 - j = 1 := by omega
  rw [h1, substring_one_strsub s j hjn]
  simp only [chrToStr, explode_implode_eq, List.reverse_singleton]

/-- Original `tokens_alt_tokens_alt_aux`: the scan-based tokenizer agrees with
`tokens_aux` at every starting point. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "tokens_alt_tokens_alt_aux"]
theorem tokensAlt_tokensAux (f : HolChar → Bool) (s : MlString) :
    ∀ (acc : List HolChar) (j l : Nat) (i : Nat), i ≤ j → j ≤ strlen s →
      strlen s - j = l → acc = (explode (substring s i (j - i))).reverse →
      tokensAux f s acc j l = tokensAltAux f s i j (strlen s) := by
  intro acc j l
  revert acc j
  induction l with
  | zero =>
      intro acc j i hij hjn hlen hacc
      have hjeq : j = strlen s := by omega
      subst j
      cases acc with
      | nil =>
          have hieq : i = strlen s :=
            (acc_nil_iff s i (strlen s) hij (by omega)).mp hacc.symm
          subst i
          rw [tokensAux, tokensAltAux.eq_def, if_neg (by omega : ¬ strlen s < strlen s)]
          rw [if_pos rfl]
      | cons h t =>
          have hhead : .implode (h :: t).reverse = substring s i (strlen s - i) := by
            rw [hacc, List.reverse_reverse, implode_explode]
          have hne : i ≠ strlen s := by
            intro heq
            have hnil : (explode (substring s i (strlen s - i))).reverse = [] :=
              (acc_nil_iff s i (strlen s) hij (by omega)).mpr heq
            rw [hnil] at hacc
            exact List.cons_ne_nil h t hacc
          rw [tokensAux, tokensAltAux.eq_def, if_neg (by omega : ¬ strlen s < strlen s)]
          rw [if_neg hne, hhead]
  | succ l ih =>
      intro acc j i hij hjn hlen hacc
      have hjn' : j < strlen s := by omega
      have hnext : strlen s - (j + 1) = l := by omega
      cases acc with
      | nil =>
          have hieq : i = j := (acc_nil_iff s i j hij hjn).mp hacc.symm
          subst i
          rw [tokensAux, tokensAltAux.eq_def, if_pos hjn']
          by_cases hf : f (strsub s j)
          · rw [if_pos hf, if_pos hf, if_pos rfl]
            refine ih [] (j + 1) (j + 1) (by omega) (by omega) hnext ?_
            rw [Nat.sub_self]
            simp only [substring_zero_len, explode_implode_eq, List.reverse_nil]
          · rw [if_neg hf, if_neg hf]
            refine ih [strsub s j] (j + 1) j (by omega) (by omega) hnext ?_
            exact singleton_eq_reverse_substring s j hjn'
      | cons h t =>
          have hne : i ≠ j := by
            intro heq
            have hnil : (explode (substring s i (j - i))).reverse = [] :=
              (acc_nil_iff s i j hij hjn).mpr heq
            rw [hnil] at hacc
            exact List.cons_ne_nil h t hacc
          rw [tokensAux, tokensAltAux.eq_def, if_pos hjn']
          by_cases hf : f (strsub s j)
          · rw [if_pos hf, if_pos hf, if_neg hne]
            have hhead : .implode (h :: t).reverse = substring s i (j - i) := by
              rw [hacc, List.reverse_reverse, implode_explode]
            have htail :
                tokensAux f s [] (j + 1) l = tokensAltAux f s (j + 1) (j + 1) (strlen s) := by
              refine ih [] (j + 1) (j + 1) (by omega) (by omega) hnext ?_
              rw [Nat.sub_self]
              simp only [substring_zero_len, explode_implode_eq, List.reverse_nil]
            rw [hhead, htail]
          · rw [if_neg hf, if_neg hf]
            have hacc' :
                strsub s j :: h :: t = (explode (substring s i (j + 1 - i))).reverse := by
              rw [hacc, explode_substring_succ s i j hij hjn', List.reverse_append]
              rw [List.reverse_singleton]
              rfl
            exact ih (strsub s j :: h :: t) (j + 1) i (by omega) (by omega) hnext hacc'

/-- Original `tokens_alt`: tokenizing the whole string from position `0`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "tokens_alt"]
theorem tokens_alt (f : HolChar → Bool) (s : MlString) :
    tokens f s = tokensAltAux f s 0 0 (strlen s) := by
  rw [tokens]
  exact tokensAlt_tokensAux f s [] 0 (strlen s) 0 (by omega) (by omega) (by omega) (by simp)

end Flapjack.Basis.Pure.MlString
