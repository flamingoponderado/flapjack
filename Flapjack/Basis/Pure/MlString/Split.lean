module

public import Flapjack.HolRef
public import Flapjack.Basis.Pure.MlString.Ops
public import Flapjack.Misc.RichList

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

/-- A substring starting at `0` is a prefix of the character list. -/
private theorem substring_zero_off (s : MlString) (len : Nat) :
    substring s 0 len = .implode ((explode s).take len) := by
  rw [substring, List.drop_zero]
  by_cases h : len ≤ strlen s
  · rw [if_pos (by simpa using h)]
  · rw [if_neg (by simpa using h)]
    have hle : strlen s ≤ len := by omega
    rw [if_pos (Nat.zero_le _)]
    rw [List.take_of_length_le (by simpa [strlen_eq_explode_length] using hle)]

/-- A substring from `i` to the end is a suffix of the character list. -/
private theorem substring_suffix (s : MlString) (i : Nat) :
    substring s i (strlen s - i) = .implode ((explode s).drop i) := by
  rw [substring]
  by_cases hi : i ≤ strlen s
  · rw [if_pos (by omega)]
    have hlen : ((explode s).drop i).length = strlen s - i := by
      rw [List.length_drop, strlen_eq_explode_length]
    rw [List.take_of_length_le (by omega)]
  · have hge : strlen s ≤ i := by omega
    rw [if_neg (by omega), if_neg (by omega)]
    rw [List.drop_eq_nil_of_le (by simpa [strlen_eq_explode_length] using hge)]

/-- Taking the minimum of the list length and a bound is the same as taking the
bound. -/
private theorem take_min (l : List HolChar) (n : Nat) :
    l.take (min l.length n) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_right h]
  · have hle : l.length ≤ n := by omega
    rw [Nat.min_eq_left hle, List.take_of_length_le hle, List.take_length]

/-- The prefix extraction is the character-list prefix. -/
private theorem extract_zero_some (s : MlString) (i : Nat) :
    extract s 0 (some i) = .implode ((explode s).take i) := by
  rw [extract]
  by_cases h : strlen s ≤ 0
  · rw [if_pos h]
    have h0 : (explode s).length = 0 := by
      simpa [strlen_eq_explode_length] using h
    rw [List.eq_nil_of_length_eq_zero h0]
    simp
  · rw [if_neg h, Nat.sub_zero, substring_zero_off, strlen_eq_explode_length, take_min]

/-- The suffix extraction is the character-list suffix. -/
private theorem extract_none (s : MlString) (i : Nat) :
    extract s i none = .implode ((explode s).drop i) := by
  rw [extract]
  by_cases h : strlen s ≤ i
  · rw [if_pos h, List.drop_eq_nil_of_le (by simpa [strlen_eq_explode_length] using h)]
  · rw [if_neg h, substring_suffix]

/-- Original `splitl_aux_SPLITP`: the scan-based splitter is the `SPLITP` split
of the suffix, prefixed by the skipped characters. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "splitl_aux_SPLITP"]
theorem splitlAux_splitP (P : HolChar → Bool) (s : MlString) (i : Nat) :
    splitlAux P s i =
      Prod.map (fun l => MlString.implode ((explode s).take i ++ l)) MlString.implode
        (splitP (fun c => !(P c)) ((explode s).drop i)) := by
  fun_induction splitlAux P s i with
  | case1 i hn ih1 =>
      rw [Bool.and_eq_true] at hn
      have hlt : i < strlen s := of_decide_eq_true hn.1
      have hp : P (strsub s i) = true := hn.2
      have hi : i < (explode s).length := by
        simpa [strlen_eq_explode_length] using hlt
      have hsub : strsub s i = (explode s)[i] := holEl_eq_getElem i (explode s) hi
      have hdrop : (explode s).drop i = strsub s i :: (explode s).drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hi, hsub]
      have htake : (explode s).take (i + 1) = (explode s).take i ++ [strsub s i] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, hsub]
        rfl
      rw [ih1, hdrop, splitP, if_neg (by simp [hp]), htake]
      simp only [List.append_assoc]
      rfl
  | case2 i hn =>
      by_cases hlt : i < strlen s
      · have hp : ¬(P (strsub s i) = true) := by
          intro hpt
          apply hn
          rw [Bool.and_eq_true]
          exact ⟨decide_eq_true_eq.mpr hlt, hpt⟩
        have hi : i < (explode s).length := by
          simpa [strlen_eq_explode_length] using hlt
        have hsub : strsub s i = (explode s)[i] := holEl_eq_getElem i (explode s) hi
        have hdrop : (explode s).drop i = strsub s i :: (explode s).drop (i + 1) := by
          rw [List.drop_eq_getElem_cons hi, hsub]
        rw [extract_zero_some, extract_none, hdrop, splitP, if_pos (by simp [hp])]
        simp
      · have hge : strlen s ≤ i := by omega
        rw [extract_zero_some, extract_none,
          List.drop_eq_nil_of_le (by simpa [strlen_eq_explode_length] using hge), splitP]
        simp

/-- Original `splitl_SPLITL`: splitting from the start is the `SPLITL` split of
the character list. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "splitl_SPLITL"]
theorem splitl_splitL (P : HolChar → Bool) (s : MlString) :
    splitl P s = Prod.map MlString.implode MlString.implode (splitL P (explode s)) := by
  rw [splitl, splitlAux_splitP, splitL, List.drop_zero, List.take_zero]
  cases splitP (fun c => !(P c)) (explode s) with
  | mk a b => rfl

/-- Original `TOKENS_def`: split a character list into maximal runs of
non-separator characters. HOL's `NULL l` test is `l = []` and `TL r` is
`r.tail`; the second pattern destructures the consumed run as a cons so its
nonemptiness is visible to the termination proof. -/
@[hol "HOL/src/string/stringScript.sml" "TOKENS_def"]
noncomputable def tokensHOL (P : HolChar → Bool) : List HolChar → List (List HolChar)
  | [] => []
  | h :: t =>
    match _hsplit : splitP P (h :: t) with
    | ([], r) => tokensHOL P r.tail
    | (a :: as, r) => (a :: as) :: tokensHOL P r
termination_by l => l.length
decreasing_by
  · have hr : r = h :: t := splitP_nil_fst P (h :: t) r _hsplit
    rw [hr]
    simp
  · have hjoin : h :: t = (a :: as) ++ r := splitP_join P (h :: t) (a :: as) r _hsplit
    rw [hjoin]
    simp only [List.length_cons, List.length_append]
    omega

/-- The empty list has no tokens. -/
private theorem tokensHOL_nil (P : HolChar → Bool) : tokensHOL P [] = [] := by
  rw [tokensHOL]

/-- A separator at the head is skipped. -/
private theorem tokensHOL_split_nil (P : HolChar → Bool) (h : HolChar) (t r : List HolChar)
    (hsp : splitP P (h :: t) = ([], r)) :
    tokensHOL P (h :: t) = tokensHOL P r.tail := by
  rw [tokensHOL, hsp]

/-- A non-separator at the head starts a new token. -/
private theorem tokensHOL_split_cons (P : HolChar → Bool) (h : HolChar) (t : List HolChar)
    (a : HolChar) (as r : List HolChar) (hsp : splitP P (h :: t) = (a :: as, r)) :
    tokensHOL P (h :: t) = (a :: as) :: tokensHOL P r := by
  rw [tokensHOL, hsp]

end Flapjack.Basis.Pure.MlString