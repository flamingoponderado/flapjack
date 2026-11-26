module

public import Flapjack.Basis.Pure.MlString
public import Flapjack.Basis.Pure.MlString.Length
public import Flapjack.Basis.Pure.MlList.Basics
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# Cake `mlstring` operations

Lean counterparts of the string operations in
`cakeml/basis/pure/mlstringScript.sml`.  HOL's `mlstring` is
`implode string` with `string = char list`, so every operation acts on the
character list behind the single constructor, with `HolChar = BitVec 8` carrying the
256 HOL characters.

`strsub` renders HOL's `EL` on a string through the ARB-completed `holEl`
(`Flapjack/Misc/ListEl.lean`), and `substring` uses `TAKE`/`DROP` for HOL's
`SEG`/`DROP`, and `«»` is `.implode []`.
-/

namespace Flapjack.Basis.Pure.MlString

open MlString Flapjack.Basis.Pure.MlList

/-- The carrier length is the length of the structural character list. -/
theorem strlen_eq_explode_length (s : MlString) : strlen s = (explode s).length := by
  cases s
  rfl

/-- Original `strsub_def`: HOL `EL` on the character list. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strsub_def"]
noncomputable def strsub (s : MlString) (n : Nat) : HolChar := holEl n (explode s)

/-- Original `substring_def`: HOL `SEG`/`DROP` with the same clamping test. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "substring_def"]
def substring (s : MlString) (off len : Nat) : MlString :=
  .implode
    (if off + len ≤ strlen s then ((explode s).drop off).take len
     else if off ≤ strlen s then (explode s).drop off
     else [])

/-- Original `extract_def`: from `i` to the end, or at most `x` characters. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "extract_def"]
def extract (s : MlString) (i : Nat) (opt : Option Nat) : MlString :=
  if strlen s ≤ i then .implode []
  else
    match opt with
    | some x => substring s i (min (strlen s - i) x)
    | none => substring s i (strlen s - i)

/-- Original `strcat_def`: concatenation of two strings. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strcat_def"]
def strcat (s1 s2 : MlString) : MlString := concat [s1, s2]

/-- Original `explode_aux_def`: the bounded walk over the character list. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_aux_def"]
noncomputable def explodeAux (s : MlString) (n : Nat) : Nat → List HolChar
  | 0 => []
  | len + 1 => strsub s n :: explodeAux s (n + 1) len

/-- Original `concatWith_def`: concatenate with a separator. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "concatWith_def"]
def concatWith (s : MlString) (l : List MlString) : MlString :=
  concat (intersperse s l)

/-- Original `chr_to_str_def`: a one-character string. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "chr_to_str_def"]
def chrToStr (c : HolChar) : MlString := .implode [c]

/-- Original `translate_aux_def`: map over a bounded prefix. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "translate_aux_def"]
noncomputable def translateAux {α : Type} (f : HolChar → α) (s : MlString) (n : Nat) :
    Nat → List α
  | 0 => []
  | len + 1 => f (strsub s n) :: translateAux f s (n + 1) len

/-- Original `translate_def`: map over the whole character list. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "translate_def"]
noncomputable def translate (f : HolChar → HolChar) (s : MlString) : MlString :=
  .implode (translateAux f s 0 (strlen s))

/-- Original `concat_nil`: the empty concatenation is the empty string. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "concat_nil"]
theorem concat_nil : concat [] = .implode [] := rfl

/-- The auxiliary walk is a `DROP` of the character list. -/
private theorem explodeAux_eq_drop (s : MlString) :
    ∀ (max n : Nat), n + max = strlen s → explodeAux s n max = (explode s).drop n
  | 0, n, h => by
    have hn : (explode s).length ≤ n := by
      simp only [strlen_eq_explode_length] at h
      omega
    simp only [explodeAux, List.drop_eq_nil_of_le hn]
  | max + 1, n, h => by
    have hn : n < (explode s).length := by
      simp only [strlen_eq_explode_length] at h
      omega
    simp only [explodeAux, strsub]
    rw [List.drop_eq_getElem_cons hn, List.cons.injEq]
    constructor
    · rw [holEl_eq_getElem n _ hn]
    · exact explodeAux_eq_drop s max (n + 1) (by omega)

/-- Original `explode_aux_thm`: the walk over a bounded suffix is `DROP`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_aux_thm"]
theorem explodeAux_eq_drop_of_length (max n : Nat) (ls : List HolChar)
    (h : n + max = ls.length) : explodeAux (.implode ls) n max = ls.drop n := by
  simpa [strlen] using explodeAux_eq_drop (.implode ls) max n (by simpa [strlen] using h)

/-- Original `explode_def`: the structural accessor is the bounded walk. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_def"]
theorem explode_eq_explodeAux (s : MlString) : explode s = explodeAux s 0 (strlen s) := by
  have h := explodeAux_eq_drop s (strlen s) 0 (by omega)
  simpa using h.symm

/-- Original `explode_thm`: exploding a constructor returns its characters. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_thm"]
theorem explode_implode_eq (ls : List HolChar) : explode (.implode ls) = ls := rfl

/-- Original `explode_11`: equal character lists give equal strings. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_11"]
theorem explode_inj (s1 s2 : MlString) : explode s1 = explode s2 ↔ s1 = s2 := by
  constructor
  · intro h
    cases s1 with
    | implode d1 =>
      cases s2 with
      | implode d2 =>
        simpa using h
  · intro h
    rw [h]

/-- The constructor is injective and surjective. HOL states this as
`BIJ implode UNIV UNIV`. The Lean conjunction is not the same statement shape, so
this stays untagged (see the task-273 progress notes). -/
theorem implode_bijective :
    Function.Injective MlString.implode ∧ Function.Surjective MlString.implode := by
  constructor
  · intro a b h
    have := congrArg explode h
    simpa using this
  · intro b
    exact ⟨explode b, by simp⟩

/-- The accessor is injective and surjective. HOL states this as
`BIJ explode UNIV UNIV`. The Lean conjunction is not the same statement shape, so
this stays untagged (see the task-273 progress notes). -/
theorem explode_bijective : Function.Injective explode ∧ Function.Surjective explode := by
  constructor
  · intro a b h
    cases a with
    | implode da =>
      cases b with
      | implode db =>
        simpa using h
  · intro b
    exact ⟨.implode b, by simp⟩

/-- Original `concat_thm`: concatenation is the flattened character lists. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "concat_thm"]
theorem concat_eq_implode_flatten (l : List MlString) :
    concat l = .implode ((l.map explode).flatten) := by
  have hcongr : List.map (fun s : MlString => match s with | .implode x => x) l
      = List.map explode l := by
    apply List.map_congr_left
    intro s _
    cases s
    rfl
  simp only [concat, hcongr]

/-- Original `strlen_implode`: the length of a constructor is its list length. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlen_implode"]
theorem strlen_implode (ls : List HolChar) : strlen (.implode ls) = ls.length := rfl

/-- Original `strlen_substring`: the length after clamping. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlen_substring"]
theorem strlen_substring (s : MlString) (i j : Nat) :
    strlen (substring s i j) =
      if i + j ≤ strlen s then j
      else if i ≤ strlen s then strlen s - i
      else 0 := by
  cases s with
  | implode data =>
    simp only [substring, strlen_eq_explode_length, explode_implode]
    by_cases h1 : i + j ≤ data.length
    · simp only [h1, if_true, List.length_take, List.length_drop]
      omega
    · simp only [h1, if_false]
      by_cases h2 : i ≤ data.length
      · simp only [h2, if_true, List.length_drop]
      · simp only [h2, if_false, List.length_nil]

/-- The clamped substring is never longer than the remaining suffix. -/
private theorem strlen_substring_le (s : MlString) (i j : Nat) :
    strlen (substring s i j) ≤ strlen s - i := by
  rw [strlen_substring]
  by_cases h1 : i + j ≤ strlen s
  · rw [if_pos h1]
    omega
  · rw [if_neg h1]
    by_cases h2 : i ≤ strlen s
    · rw [if_pos h2]
      omega
    · rw [if_neg h2]
      omega

/-- Original `strlen_extract_le`: the extraction fits in the remaining suffix. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlen_extract_le"]
theorem strlen_extract_le (s : MlString) (x : Nat) (y : Option Nat) :
    strlen (extract s x y) ≤ strlen s - x := by
  unfold extract
  split
  · simp only [strlen_eq_explode_length, explode_implode, List.length_nil]
    omega
  · split
    · exact strlen_substring_le s x _
    · exact strlen_substring_le s x _

/-- `holEl` of a long-enough prefix is `holEl` of the whole list. -/
private theorem holEl_take_eq (l : List HolChar) {m n : Nat} (hmn : m < n) :
    holEl m (l.take n) = holEl m l := by
  by_cases hm : m < l.length
  · rw [holEl_eq_getElem m (l.take n) (by
        simp only [List.length_take]
        omega),
      holEl_eq_getElem m l hm, List.getElem_take]
  · rw [holEl_of_length_le m l (by omega),
      holEl_of_length_le m (l.take n) (by
        simp only [List.length_take]
        omega)]

/-- Original `strsub_substring_0_thm`: taking from the front preserves indices. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strsub_substring_0_thm"]
theorem strsub_substring_zero (m n : Nat) (l : MlString) (h : m < n) :
    strsub (substring l 0 n) m = strsub l m := by
  cases l with
  | implode data =>
    by_cases h1 : n ≤ data.length
    · simp only [strsub, substring, strlen_eq_explode_length, explode_implode, Nat.zero_add,
        if_pos h1,
        List.drop_zero]
      exact holEl_take_eq data h
    · simp only [strsub, substring, strlen_eq_explode_length, explode_implode, Nat.zero_add,
        if_neg h1,
        if_pos (Nat.zero_le _), List.drop_zero]

/-- Original `substring_full`: the whole string is its own substring. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "substring_full"]
theorem substring_full (s : MlString) : substring s 0 (strlen s) = s := by
  cases s with
  | implode data =>
    simp only [substring, strlen_eq_explode_length, explode_implode, Nat.zero_add,
      if_pos (Nat.le_refl _),
      List.drop_zero, List.take_length]

/-- Original `substring_too_long`: an offset past the end gives the empty string. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "substring_too_long"]
theorem substring_too_long (s : MlString) (i j : Nat) (h : strlen s ≤ i) :
    substring s i j = .implode [] := by
  cases s with
  | implode data =>
    have hs : strlen (.implode data) = data.length := strlen_implode data
    rw [substring]
    by_cases h1 : i + j ≤ strlen (.implode data)
    · have hj : j = 0 := by omega
      simp only [if_pos h1]
      simp only [hj, List.take_zero]
    · by_cases h2 : i ≤ strlen (.implode data)
      · have hi : i = data.length := by omega
        simp only [if_neg h1, if_pos h2]
        simp only [explode_implode, hi, List.drop_length]
      · simp only [if_neg h1, if_neg h2]

/-- Original `concat_cons`: prepending a string prepends its characters. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "concat_cons"]
theorem concat_cons (h : MlString) (t : List MlString) :
    concat (h :: t) = strcat h (concat t) := by
  cases h with
  | implode data =>
    simp [concat, strcat]

/-- Original `strcat_thm`: concatenation appends the character lists. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strcat_thm"]
theorem strcat_eq_implode_append (s1 s2 : MlString) :
    strcat s1 s2 = .implode (explode s1 ++ explode s2) := by
  cases s1 with
  | implode d1 =>
    cases s2 with
    | implode d2 =>
      simp [strcat, concat]

/-- Original `explode_strcat`: concatenation appends the character lists. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_strcat"]
theorem explode_strcat (s1 s2 : MlString) :
    explode (strcat s1 s2) = explode s1 ++ explode s2 := by
  simp only [strcat_eq_implode_append, explode_implode]

/-- Original `strcat_assoc`: concatenation is associative. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strcat_assoc"]
theorem strcat_assoc (s1 s2 s3 : MlString) :
    strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3 := by
  simp only [strcat_eq_implode_append, explode_implode, List.append_assoc]

/-- Original `strcat_o`: composing concatenations is a concatenation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strcat_o"]
theorem strcat_comp (x y : MlString) : strcat x ∘ strcat y = strcat (strcat x y) := by
  funext z
  simp only [Function.comp_apply, strcat_assoc]

/-- Original `strcat_nil`: the empty string is a unit of concatenation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strcat_nil"]
theorem strcat_nil (s : MlString) :
    (strcat (.implode []) s = s) ∧ (strcat s (.implode []) = s) := by
  constructor
  · simp only [strcat_eq_implode_append, explode_implode, List.nil_append]
    cases s
    rfl
  · simp only [strcat_eq_implode_append, explode_implode, List.append_nil]
    cases s
    rfl

/-- Original `mlstring_common_prefix`: a common prefix cancels. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_common_prefix"]
theorem strcat_cancel_left (s t1 t2 : MlString) : strcat s t1 = strcat s t2 ↔ t1 = t2 := by
  constructor
  · intro h
    have hc := congrArg explode h
    simp only [strcat_eq_implode_append, explode_implode] at hc
    exact (explode_inj t1 t2).mp (List.append_cancel_left hc)
  · intro h
    rw [h]

/-- Original `mlstring_common_char_prefix`: a common leading character cancels
from both sides. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_common_char_prefix"]
theorem strcat_cons_eq (c1 c2 : HolChar) (s1 s2 : List HolChar) (t1 t2 : MlString) :
    strcat (.implode (c1 :: s1)) t1 = strcat (.implode (c2 :: s2)) t2 ↔
      c1 = c2 ∧ strcat (.implode s1) t1 = strcat (.implode s2) t2 := by
  simp only [strcat_eq_implode_append, explode_implode, List.cons_append, List.cons.injEq,
    MlString.implode.injEq]

/-- Original `mlstring_common_suffix`: a common suffix cancels. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring_common_suffix"]
theorem strcat_cancel_right (s t1 t2 : MlString) : strcat t1 s = strcat t2 s ↔ t1 = t2 := by
  constructor
  · intro h
    have hc := congrArg explode h
    simp only [strcat_eq_implode_append, explode_implode] at hc
    exact (explode_inj t1 t2).mp (List.append_cancel_right hc)
  · intro h
    rw [h]

/-- Original `concat_append`: concatenation distributes over list append. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "concat_append"]
theorem concat_append (xs ys : List MlString) :
    concat (xs ++ ys) = strcat (concat xs) (concat ys) := by
  induction xs with
  | nil => simp only [List.nil_append, concat_nil, strcat_nil]
  | cons x xs ih =>
    simp only [List.cons_append, concat_cons, ih, strcat_assoc]

/-- Original `implode_STRCAT`: imploding an append is a concatenation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "implode_STRCAT"]
theorem implode_append (l1 l2 : List HolChar) :
    .implode (l1 ++ l2) = strcat (.implode l1) (.implode l2) := by
  simp only [strcat_eq_implode_append, explode_implode]

/-- Original `strlen_strcat`: lengths add under concatenation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlen_strcat"]
theorem strlen_strcat (s1 s2 : MlString) : strlen (strcat s1 s2) = strlen s1 + strlen s2 := by
  simp only [strlen_eq_explode_length, explode_strcat, List.length_append]

/-- Original `explode_toString`: a one-character string explodes to that character. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "explode_toString"]
theorem explode_chrToStr (c : HolChar) : explode (chrToStr c) = [c] := rfl

/-- Original `strlen_toString`: a one-character string has length one. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlen_toString"]
theorem strlen_chrToStr (c : HolChar) : strlen (chrToStr c) = 1 := rfl

/-- The bounded translation walk is a map over a `DROP`. -/
private theorem translateAux_eq_map_drop {α : Type} (f : HolChar → α) (s : MlString) :
    ∀ (len n : Nat), n + len = strlen s →
      translateAux f s n len = ((explode s).drop n).map f
  | 0, n, h => by
    have hn : (explode s).length ≤ n := by
      simp only [strlen_eq_explode_length] at h
      omega
    simp only [translateAux, List.drop_eq_nil_of_le hn, List.map_nil]
  | len + 1, n, h => by
    have hn : n < (explode s).length := by
      simp only [strlen_eq_explode_length] at h
      omega
    simp only [translateAux, strsub]
    rw [List.drop_eq_getElem_cons hn, List.map_cons, List.cons.injEq]
    constructor
    · rw [holEl_eq_getElem n _ hn]
    · exact translateAux_eq_map_drop f s len (n + 1) (by omega)

/-- Original `translate_thm`: translation is a map over the characters. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "translate_thm"]
theorem translate_eq_implode_map (f : HolChar → HolChar) (s : MlString) :
    translate f s = .implode ((explode s).map f) := by
  unfold translate
  have h := translateAux_eq_map_drop f s (strlen s) 0 (by omega)
  simpa using h

/-- Original `exists_mlstring`: quantification over strings is quantification
over their character lists. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "exists_mlstring"]
theorem exists_mlstring (P : MlString → Bool) :
    (∃ x : MlString, P x = true) ↔ ∃ s : List HolChar, P (.implode s) = true := by
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | implode data => exact ⟨data, hx⟩
  · rintro ⟨s, hs⟩
    exact ⟨.implode s, hs⟩

/-- Original `strlit_STRCAT`: concatenating two literals concatenates their
character lists. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlit_STRCAT"]
theorem strlit_STRCAT (a b : List HolChar) :
    strcat (.implode a) (.implode b) = .implode (a ++ b) := by
  rw [strcat_eq_implode_append]
  rfl

/-- Original `substring_0`: a zero-length substring is empty. -/
@[simp, hol "cakeml/basis/pure/mlstringScript.sml" "substring_0"]
theorem substring_zero (s : MlString) (i : Nat) : substring s i 0 = .implode [] := by
  unfold substring
  split
  · simp
  · split
    · omega
    · simp

end Flapjack.Basis.Pure.MlString
