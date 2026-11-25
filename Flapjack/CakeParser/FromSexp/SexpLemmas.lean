module

public import Flapjack.CakeParser.FromSexp.RoundTrip

@[expose] public section

-- Public statements below name private encoding helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Simple-S-expression list and option-destruction lemmas

Lean counterparts of the `fromSexp` statements about HOL's `simpleSexp`
helpers `strip_sxcons` and `dstrip_sexp`, together with the option-destruction
functions `odestSXSTR`, `odestSXSYM` and `odestSXNUM` and the list-encoding
laws (`listsexp_thm`, `listsexp_MAP_EQ_f`, `FOLDR_SX_CONS_INJ`,
`OPTION_CHOICE_EQ_SOME`) in `cakeml/compiler/parsing/fromSexpScript.sml`.

`stripSxCons` is untagged infrastructure: it is HOL's `simpleSexp$strip_sxcons`,
which lives outside `cakeml/`.  It agrees definitionally with `decodeList some`.
`nil` is `SX_SYM "nil"`, spelled `nilSexp` here.
-/

namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString

private def ascii (s : String) : List HolChar := (ofString s).explode

/-- HOL `nil`: the symbol `nil`, which is also the empty encoded list. -/
abbrev nilSexp : Sexp := listsexp []

/-- HOL `simpleSexp$strip_sxcons`: the elements of a proper list, or `none`. -/
def stripSxCons : Sexp → Option (List Sexp)
  | .cons h t => (stripSxCons t).map (h :: ·)
  | .sym name => if name == ascii "nil" then some [] else none
  | _ => none

/-- The identity list decoder and `stripSxCons` agree. -/
private theorem stripSxCons_eq_decodeList (s : Sexp) : stripSxCons s = decodeList some s := by
  induction s with
  | cons h t _ ihT =>
    simp only [stripSxCons, decodeList]
    rw [ihT]
    cases decodeList some t with
    | none => rfl
    | some v => rfl
  | sym name => rfl
  | num _ => rfl
  | str _ => rfl

/-- Original `odestSXSTR_def`: the bytes of a string S-expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSTR_def"]
def odestSXSTR : Sexp → Option MlString
  | .str s => some (MlString.implode s)
  | _ => none

/-- Original `odestSXSYM_def`: the bytes of a symbol S-expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSYM_def"]
def odestSXSYM : Sexp → Option MlString
  | .sym s => some (MlString.implode s)
  | _ => none

/-- Original `odestSXNUM_def`: the number of a numeric S-expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXNUM_def"]
def odestSXNUM : Sexp → Option Nat
  | .num n => some n
  | _ => none

/-- Original `odestSXNUM_SEXSTR`: an encoded string is never a number. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXNUM_SEXSTR"]
theorem odestSXNUM_sexstr (str : List HolChar) : odestSXNUM (sexstr str) = none := rfl

/-- Original `odestSXSTR_SOME`: string destruction succeeds exactly on `.str`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSTR_SOME"]
theorem odestSXSTR_some (s : Sexp) (y : MlString) :
    (odestSXSTR s = some y ↔ s = .str y.explode) ∧
      (some y = odestSXSTR s ↔ s = .str y.explode) := by
  cases s with
  | sym _ => simp [odestSXSTR]
  | num _ => simp [odestSXSTR]
  | str bytes =>
    simp only [odestSXSTR, Option.some.injEq, Sexp.str.injEq]
    constructor
    · constructor
      · intro h
        rw [← h]
        simp
      · intro h
        rw [h]
        simp
    · constructor
      · intro h
        rw [h]
        simp
      · intro h
        rw [h]
        simp
  | cons _ _ => simp [odestSXSTR]

/-- Original `odestSXNUM_SOME`: number destruction succeeds exactly on `.num`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXNUM_SOME"]
theorem odestSXNUM_some (s : Sexp) (n : Nat) :
    (odestSXNUM s = some n ↔ s = .num n) ∧ (some n = odestSXNUM s ↔ s = .num n) := by
  cases s with
  | sym _ => simp [odestSXNUM]
  | num _ => simp [odestSXNUM, eq_comm]
  | str _ => simp [odestSXNUM]
  | cons _ _ => simp [odestSXNUM]

/-- Original `odestSXSTR_SX_STR`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSTR_SX_STR"]
theorem odestSXSTR_sx_str (s : List HolChar) :
    odestSXSTR (.str s) = some (MlString.implode s) := rfl

/-- Original `odestSXNUM_SX_NUM`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXNUM_SX_NUM"]
theorem odestSXNUM_sx_num (n : Nat) : odestSXNUM (.num n) = some n := rfl

/-- Original `odestSXSYM_SX_SYM`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSYM_SX_SYM"]
theorem odestSXSYM_sx_sym (s : List HolChar) :
    odestSXSYM (.sym s) = some (MlString.implode s) := rfl

/-- Original `odestSXSTR_listsexp`: an encoded list is not a string. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSTR_listsexp"]
theorem odestSXSTR_listsexp (l : List Sexp) : odestSXSTR (listsexp l) = none := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

/-- Original `odestSEXSTR_listsexp`: an encoded list is not a string. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSEXSTR_listsexp"]
theorem odestSEXSTR_listsexp (l : List Sexp) : destString (listsexp l) = none := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

/-- Original `odestSXNUM_listsexp`: an encoded list is not a number. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXNUM_listsexp"]
theorem odestSXNUM_listsexp (l : List Sexp) : odestSXNUM (listsexp l) = none := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

/-- Original `strip_sxcons_SOME_NIL`: only `nil` strips to the empty list. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "strip_sxcons_SOME_NIL"]
theorem stripSxCons_some_nil (s : Sexp) : stripSxCons s = some [] ↔ s = nilSexp := by
  rw [stripSxCons_eq_decodeList, decodeList_some_identity]

/-- Original `strip_sxcons_EQ_CONS`: a nonempty strip is a cons cell. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "strip_sxcons_EQ_CONS"]
theorem stripSxCons_eq_cons (s : Sexp) (h : Sexp) (t : List Sexp) :
    stripSxCons s = some (h :: t) ↔
      ∃ s0, s = .cons h s0 ∧ stripSxCons s0 = some t := by
  rw [stripSxCons_eq_decodeList, decodeList_some_identity]
  simp only [stripSxCons_eq_decodeList, decodeList_some_identity, listsexp]
  constructor
  · intro hc
    exact ⟨listsexp t, hc, rfl⟩
  · rintro ⟨s0, rfl, rfl⟩
    rfl

/-- Original `strip_sxcons_listsexp`: stripping an encoded list returns it. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "strip_sxcons_listsexp"]
theorem stripSxCons_listsexp (ls : List Sexp) : stripSxCons (listsexp ls) = some ls := by
  rw [stripSxCons_eq_decodeList]
  exact (decodeList_some_identity (listsexp ls) ls).mpr rfl

/-- Original `dstrip_sexp_listsexp`: stripping an encoded list is the source
list's head symbol, if any. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "dstrip_sexp_listsexp"]
theorem stripConstructor_listsexp (ls : List Sexp) :
    stripConstructor (listsexp ls) =
      (match ls with
        | .sym x :: xs => some (x, xs)
        | _ => none) := by
  cases ls with
  | nil => rfl
  | cons x xs =>
    cases x with
    | sym name =>
        have hd : decodeList some (listsexp xs) = some xs := by
          simpa using decodeList_listsexp some id xs (by simp)
        simp only [listsexp] at hd ⊢
        simp [stripConstructor, hd]
    | num _ => rfl
    | str _ => rfl
    | cons _ _ => rfl

/-- Original `dstrip_sexp_SX_STR`: a string is not a constructor. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "dstrip_sexp_SX_STR"]
theorem stripConstructor_str (s : List HolChar) : stripConstructor (.str s) = none := rfl

/-- Original `dstrip_sexp_SEXSTR`: an encoded string is not a constructor. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "dstrip_sexp_SEXSTR"]
theorem stripConstructor_sexstr (s : List HolChar) : stripConstructor (sexstr s) = none := rfl

/-- Original `dstrip_sexp_SOME`: a successful strip is a symbol applied to a
proper argument list. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "dstrip_sexp_SOME"]
theorem stripConstructor_some_iff (s : Sexp) (x : List HolChar × List Sexp) :
    stripConstructor s = some x ↔
      ∃ sym sa args, s = .cons (.sym sym) sa ∧ stripSxCons sa = some args ∧
        x = (sym, args) := by
  obtain ⟨sym, args⟩ := x
  constructor
  · intro h
    have hs : s = .cons (.sym sym) (listsexp args) := (stripConstructor_some s sym args).mp h
    exact ⟨sym, listsexp args, args, hs, stripSxCons_listsexp args, rfl⟩
  · rintro ⟨sym2, sa, args2, hs, hstrip, hx⟩
    have hsa : sa = listsexp args2 := by
      rw [stripSxCons_eq_decodeList] at hstrip
      exact (decodeList_some_identity sa args2).mp hstrip
    have h1 : sym = sym2 := congrArg Prod.fst hx
    have h2 : args = args2 := congrArg Prod.snd hx
    rw [h1, h2]
    exact (stripConstructor_some s sym2 args2).mpr (by rw [hs, hsa])

/-- Original `listsexp_thm`: the encoded empty list and cons equation. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "listsexp_thm"]
theorem listsexp_eq (h : Sexp) (t : List Sexp) :
    listsexp [] = nilSexp ∧ listsexp (h :: t) = .cons h (listsexp t) :=
  ⟨rfl, rfl⟩

/-- Original `listsexp_MAP_EQ_f`: pointwise-equal maps encode equally. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "listsexp_MAP_EQ_f"]
theorem listsexp_map_eq {α : Type} (ls : List α) (f1 f2 : α → Sexp)
    (h : ∀ x, x ∈ ls → f1 x = f2 x) : listsexp (ls.map f1) = listsexp (ls.map f2) := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    have ih' : listsexp (xs.map f1) = listsexp (xs.map f2) :=
      ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, listsexp]
    rw [h x (by simp)]
    change Sexp.cons (f2 x) (listsexp (xs.map f1)) =
      Sexp.cons (f2 x) (listsexp (xs.map f2))
    rw [ih']

/-- Original `FOLDR_SX_CONS_INJ`: the list encoding is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "FOLDR_SX_CONS_INJ"]
theorem foldr_cons_injective (l1 l2 : List Sexp) : listsexp l1 = listsexp l2 ↔ l1 = l2 :=
  listsexp_injective l1 l2

/-- Original `OPTION_CHOICE_EQ_SOME`: `++` on options succeeds on either side. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "OPTION_CHOICE_EQ_SOME"]
theorem option_choice_eq_some {α : Type} (x y : Option α) (z : α) :
    ((x <|> y) = some z) ↔ x = some z ∨ (x = none ∧ y = some z) := by
  cases x with
  | none => simp
  | some val => simp

end Flapjack.CakeParser.FromSexp
