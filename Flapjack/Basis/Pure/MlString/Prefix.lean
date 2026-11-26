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

/-- Original `str_findi_def`: the first index from `i` whose character
satisfies `P`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "str_findi_def"]
noncomputable def strFindi (P : HolChar → Bool) (i : Nat) (s : MlString) : Option Nat :=
  if i < strlen s then
    if P (strsub s i) then some i else strFindi P (i + 1) s
  else none
termination_by strlen s - i
decreasing_by
  omega

/-- Original `str_findi_range`: a found index is within the string. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "str_findi_range"]
theorem strFindi_range (j : Nat) :
    ∀ (P : HolChar → Bool) (i : Nat) (s : MlString),
      strFindi P i s = some j → i ≤ j ∧ j < strlen s := by
  intro P i s h
  fun_induction strFindi P i s with
  | case1 x hlt hp =>
      simp only [Option.some.injEq] at h
      omega
  | case2 x hlt hn ih =>
      have := ih h
      omega
  | case3 x hn =>
      simp at h

/-- Original `isStringThere_SEG`: comparing `n` characters from two offsets is
equal SEGs. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isStringThere_SEG"]
theorem isStringThere_SEG (s1 s2 : List HolChar) (i1 i2 n : Nat)
    (h1 : i1 + n ≤ s1.length) (h2 : i2 + n ≤ s2.length) :
    (isStringThereAux (.implode s1) (.implode s2) i1 i2 n = true ↔
      (s1.drop i1).take n = (s2.drop i2).take n) := by
  induction n generalizing i1 i2 with
  | zero => simp only [isStringThereAux, List.take_zero]
  | succ n ih =>
    have hi1 : i1 < s1.length := by omega
    have hi2 : i2 < s2.length := by omega
    have hsub1 : strsub (.implode s1) i1 = s1[i1] := holEl_eq_getElem i1 s1 hi1
    have hsub2 : strsub (.implode s2) i2 = s2[i2] := holEl_eq_getElem i2 s2 hi2
    have htake1 : (s1.drop i1).take (n + 1) = s1[i1] :: (s1.drop (i1 + 1)).take n := by
      rw [List.drop_eq_getElem_cons hi1, List.take_succ_cons]
    have htake2 : (s2.drop i2).take (n + 1) = s2[i2] :: (s2.drop (i2 + 1)).take n := by
      rw [List.drop_eq_getElem_cons hi2, List.take_succ_cons]
    have hrec := ih (i1 + 1) (i2 + 1) (by omega) (by omega)
    rw [htake1, htake2]
    rw [isStringThereAux]
    simp only [hsub1, hsub2]
    by_cases heq : s1[i1] = s2[i2]
    · rw [if_pos heq, List.cons.injEq]
      simp only [heq, true_and]
      exact hrec
    · rw [if_neg heq]
      simp only [Bool.false_eq_true, false_iff, List.cons.injEq]
      intro h
      exact heq h.1

/-- Original `isSubstring_aux_lemma`: a successful scan finds an occurrence. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isSubstring_aux_lemma"]
theorem isSubstringAux_iff (s1 s2 : MlString) (lens1 i len : Nat)
    (h : i + len ≤ strlen s2) :
    (isSubstringAux s1 s2 lens1 i len = true ↔
      ∃ n, n < len ∧ isStringThereAux s1 s2 0 (n + i) lens1 = true) := by
  induction len generalizing i with
  | zero => simp [isSubstringAux]
  | succ len ih =>
    have hrec := ih (i + 1) (by omega)
    simp only [isSubstringAux]
    by_cases hthere : isStringThereAux s1 s2 0 i lens1 = true
    · rw [if_pos hthere]
      exact ⟨fun _ => ⟨0, by omega, by simpa using hthere⟩, fun _ => rfl⟩
    · rw [if_neg hthere, hrec]
      constructor
      · rintro ⟨n, hn, hc⟩
        exact ⟨n + 1, by omega,
          by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc⟩
      · rintro ⟨n, hn, hc⟩
        cases n with
        | zero => exact absurd (by simpa using hc) hthere
        | succ k => exact ⟨k, by omega,
            by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc⟩

/-- Original `isSubstring_SEG`: a substring occurs exactly when some SEG of the
longer string equals it. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "isSubstring_SEG"]
theorem isSubstring_SEG (s1 s2 : List HolChar) :
    (isSubstring (.implode s1) (.implode s2) = true ↔
      ∃ i, i + s1.length ≤ s2.length ∧ (s2.drop i).take s1.length = s1) := by
  cases s1 with
  | nil =>
    constructor
    · intro _
      exact ⟨0, by simp⟩
    · intro _
      simp [isSubstring, isSubstringAux]
      exact ⟨Nat.zero_le _, Or.inl rfl⟩
  | cons h t =>
    unfold isSubstring
    split
    · rename_i hlen
      have hlen' : (h :: t).length ≤ s2.length := by
        simpa only [strlen_implode] using hlen
      have hbound : 0 + (s2.length - (h :: t).length + 1) ≤ s2.length := by
        simp only [List.length_cons] at hlen' ⊢
        omega
      simp only [strlen_implode]
      rw [isSubstringAux_iff (.implode (h :: t)) (.implode s2) (h :: t).length 0
        (s2.length - (h :: t).length + 1) hbound]
      constructor
      · rintro ⟨n, hn, hthere⟩
        have hseg : ((h :: t).drop 0).take (h :: t).length =
            (s2.drop n).take (h :: t).length :=
          (isStringThere_SEG (h :: t) s2 0 n (h :: t).length (by omega) (by omega)).mp hthere
        have hleft : ((h :: t).drop 0).take (h :: t).length = h :: t := by simp
        exact ⟨n, by omega, by rw [← hseg, hleft]⟩
      · rintro ⟨i, hi, hseg⟩
        have hleft : ((h :: t).drop 0).take (h :: t).length = h :: t := by simp
        refine ⟨i, by omega, ?_⟩
        exact (isStringThere_SEG (h :: t) s2 0 i (h :: t).length (by omega) (by omega)).mpr
          (by rw [hleft, hseg])
    · rename_i hlen
      have hlen' : s2.length < (h :: t).length := by
        simp only [strlen_implode] at hlen
        omega
      constructor
      · intro hx
        exact absurd hx (by simp)
      · rintro ⟨i, hi, _⟩
        omega

end Flapjack.Basis.Pure.MlString
