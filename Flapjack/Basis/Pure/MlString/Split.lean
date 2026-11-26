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

end Flapjack.Basis.Pure.MlString
