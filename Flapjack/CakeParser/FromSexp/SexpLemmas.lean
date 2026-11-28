module

public import Flapjack.CakeParser.FromSexp.RoundTrip
public import Flapjack.Misc.ListEl

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
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString Flapjack.AstHOL

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

/-- Original `strip_sxcons_thm`: the strip clauses for cons cells, numbers,
strings and symbols. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "strip_sxcons_thm"]
theorem stripSxCons_eq (h t : Sexp) (n : Nat) (s str : List HolChar) :
    stripSxCons (.cons h t) = (stripSxCons t).map (h :: ·) ∧
      stripSxCons (.num n) = none ∧
      stripSxCons (.str str) = none ∧
      stripSxCons (.sym s) = (if s == nilBytes then some [] else none) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

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

/-- Original `dstrip_sexp_thm`: the constructor-strip clauses. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "dstrip_sexp_thm"]
theorem stripConstructor_eq (s : List HolChar) (args : Sexp) (n : Nat)
    (s1 s2 : Sexp) (str : List HolChar) :
    stripConstructor (.cons (.sym s) args) =
        (stripSxCons args).map (fun t => (s, t)) ∧
      stripConstructor (.cons (.num n) args) = none ∧
      stripConstructor (.cons (.str str) args) = none ∧
      stripConstructor (.cons (.cons s1 s2) args) = none ∧
      stripConstructor (.num n) = none ∧
      stripConstructor (.sym s) = none ∧
      stripConstructor (.str str) = none := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [stripSxCons_eq_decodeList]
  cases hd : decodeList some args with
  | none =>
    simp only [stripConstructor, hd]
    rfl
  | some v =>
    simp only [stripConstructor, hd]
    rfl

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

/-- Original `odestSXSYM_EQ_SOME`: symbol destruction succeeds exactly on `.sym`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXSYM_EQ_SOME"]
theorem odestSXSYM_eq_some (s : Sexp) (str : MlString) :
    (odestSXSYM s = some str ↔ s = .sym str.explode) ∧
      (some str = odestSXSYM s ↔ s = .sym str.explode) := by
  cases s with
  | sym bytes =>
    simp only [odestSXSYM, Option.some.injEq, Sexp.sym.injEq]
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
  | num _ => simp [odestSXSYM]
  | str _ => simp [odestSXSYM]
  | cons _ _ => simp [odestSXSYM]

/-- Original `odestSXNUM_EQ_SOME`: number destruction succeeds exactly on `.num`. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSXNUM_EQ_SOME"]
theorem odestSXNUM_eq_some (s : Sexp) (n : Nat) :
    (odestSXNUM s = some n ↔ s = .num n) ∧ (some n = odestSXNUM s ↔ s = .num n) := by
  cases s with
  | sym _ => simp [odestSXNUM]
  | num _ => simp [odestSXNUM, eq_comm]
  | str _ => simp [odestSXNUM]
  | cons _ _ => simp [odestSXNUM]

/-- Original `strip_sxcons_11`: a successful strip determines its input. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "strip_sxcons_11"]
theorem stripSxCons_inj (s1 s2 : Sexp) (x : List Sexp)
    (h : stripSxCons s1 = some x ∧ stripSxCons s2 = some x) : s1 = s2 := by
  obtain ⟨h1, h2⟩ := h
  rw [stripSxCons_eq_decodeList] at h1 h2
  have e1 : s1 = listsexp x := (decodeList_some_identity s1 x).mp h1
  have e2 : s2 = listsexp x := (decodeList_some_identity s2 x).mp h2
  rw [e1, e2]

/-- Original `sexplist_thm`: the list-decoder clauses. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplist_thm"]
theorem decodeList_eq {α : Type} (p : Sexp → Option α) (h t : Sexp) (s str : List HolChar)
    (n : Nat) :
    decodeList p (.cons h t) =
        (do
          let ph ← p h
          let pt ← decodeList p t
          some (ph :: pt)) ∧
      decodeList p (.sym s) = (if s == nilBytes then some [] else none) ∧
      decodeList p (.num n) = none ∧ decodeList p (.str str) = none := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp only [decodeList]
  rw [ascii_nil_eq_nilBytes]

/-- Original `sexplist_listsexp_matchable`: decoding an encoded list recovers it. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplist_listsexp_matchable"]
theorem decodeList_listsexp_matchable {α : Type} (g : α → Sexp) (gl : List Sexp)
    (l : List α) (f : Sexp → Option α)
    (h : ∀ x, x ∈ l → f (g x) = some x) (hgl : gl = l.map g) :
    decodeList f (listsexp gl) = some l := by
  subst hgl
  exact decodeList_listsexp f g l h

/-- Original `decode_thunk_mode_def`: parse a thunk-mode name. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decode_thunk_mode_def"]
def decodeThunkMode (s : List HolChar) : Option ThunkMode :=
  if s = (ofString "Evaluated").explode then some .evaluated
  else if s = (ofString "NotEvaluated").explode then some .notEvaluated
  else none

/-- Original `encode_thunk_mode_def`: the thunk-mode names. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "encode_thunk_mode_def"]
def encodeThunkMode : ThunkMode → List HolChar
  | .evaluated => (ofString "Evaluated").explode
  | .notEvaluated => (ofString "NotEvaluated").explode

/-- HOL `OPTION_APPLY` (printed `<*>`): apply an optional function. -/
def optionApply {α β : Type} (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind fun g => x.map g

/-- Original `OPTION_APPLY_MAP3`: three applications succeed componentwise. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "OPTION_APPLY_MAP3"]
theorem optionApply_map3 {α β γ δ : Type} (f : δ → γ → β → α) (x : Option δ)
    (y : Option γ) (z : Option β) (r : α) :
    optionApply (optionApply (x.map f) y) z = some r ↔
      ∃ a b c, x = some a ∧ y = some b ∧ z = some c ∧ f a b c = r := by
  cases x with
  | none => simp [optionApply]
  | some a =>
    cases y with
    | none => simp [optionApply]
    | some b =>
      cases z with
      | none => simp [optionApply]
      | some c => simp [optionApply]

/-- Original `OPTION_APPLY_MAP4`: four applications succeed componentwise. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "OPTION_APPLY_MAP4"]
theorem optionApply_map4 {α β γ δ ε : Type} (f : ε → δ → γ → β → α) (x : Option ε)
    (y : Option δ) (z : Option γ) (t : Option β) (r : α) :
    optionApply (optionApply (optionApply (x.map f) y) z) t = some r ↔
      ∃ a b c d, x = some a ∧ y = some b ∧ z = some c ∧ t = some d ∧ f a b c d = r := by
  cases x with
  | none => simp [optionApply]
  | some a =>
    cases y with
    | none => simp [optionApply]
    | some b =>
      cases z with
      | none => simp [optionApply]
      | some c =>
        cases t with
        | none => simp [optionApply]
        | some d => simp [optionApply]

/-- Original `monad_bind_FAIL`: binding into failure is failure. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "monad_bind_FAIL"]
theorem option_bind_fail {α β : Type} (m1 : Option β) :
    m1.bind (fun _ => (none : Option α)) = none := by
  cases m1 with
  | none => rfl
  | some _ => rfl

/-- Original `monad_unitbind_CONG`: unit-binding respects both arguments. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "monad_unitbind_CONG"]
theorem option_unitbind_cong {α : Type} (m11 m12 : Option Unit) (m21 m22 : Option α)
    (h1 : m11 = m12) (h2 : m12 = some () → m21 = m22) :
    m11.bind (fun _ => m21) = m12.bind (fun _ => m22) := by
  rw [h1]
  cases m12 with
  | none => rfl
  | some u =>
    cases u
    have h21 : m21 = m22 := h2 rfl
    rw [h21]

/-- Original `strip_sxcons_FAIL_sexplist_FAIL`: a failed strip means a failed
list decode. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "strip_sxcons_FAIL_sexplist_FAIL"]
theorem stripSxCons_fail_decodeList_fail {α : Type} (s : Sexp) (p : Sexp → Option α)
    (h : stripSxCons s = none) : decodeList p s = none := by
  cases hd : decodeList p s with
  | none => rfl
  | some l =>
    obtain ⟨ys, rfl, _⟩ := (decodeList_some p s l).mp hd
    rw [stripSxCons_listsexp] at h
    exact absurd h (by simp)

/-- Original `sexppair_CONG`: pair decoding respects pointwise-equal decoders. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexppair_CONG"]
theorem decodePair_cong {α β : Type} (s1 s2 : Sexp) (p1 p1' : Sexp → Option α)
    (p2 p2' : Sexp → Option β)
    (h : s1 = s2 ∧
      (∀ s, (∃ s', s2 = .cons s s') → p1 s = p1' s) ∧
      (∀ s, (∃ s', s2 = .cons s' s) → p2 s = p2' s)) :
    decodePair p1 p2 s1 = decodePair p1' p2' s2 := by
  obtain ⟨h12, h1, h2⟩ := h
  rw [h12]
  cases s2 with
  | cons a b =>
    have ha : p1 a = p1' a := h1 a ⟨b, rfl⟩
    have hb : p2 b = p2' b := h2 b ⟨a, rfl⟩
    simp [decodePair, ha, hb]
  | sym _ => simp [decodePair]
  | num _ => simp [decodePair]
  | str _ => simp [decodePair]

/-- HOL `simpleSexp$sxMEM`: the element occurs in the stripped list. -/
def sxMem (e s : Sexp) : Bool :=
  match stripSxCons s with
  | some l => decide (e ∈ l)
  | none => false

/-- Original `sexplist_CONG`: list decoding respects pointwise-equal decoders. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplist_CONG"]
theorem decodeList_cong {α : Type} (s1 s2 : Sexp) (p1 p2 : Sexp → Option α)
    (h : s1 = s2 ∧ ∀ e, sxMem e s2 = true → p1 e = p2 e) :
    decodeList p1 s1 = decodeList p2 s2 := by
  obtain ⟨h12, h⟩ := h
  rw [h12]
  have key : ∀ s, (∀ e, sxMem e s = true → p1 e = p2 e) →
      decodeList p1 s = decodeList p2 s := by
    intro s
    induction s with
    | cons head tail _ ih =>
      intro hs
      cases ht : stripSxCons tail with
      | none =>
        have h1 := stripSxCons_fail_decodeList_fail tail p1 ht
        have h2 := stripSxCons_fail_decodeList_fail tail p2 ht
        simp [decodeList, h1, h2]
      | some l =>
        have hhead : p1 head = p2 head := by
          apply hs head
          simp [sxMem, stripSxCons, ht]
        have htail : decodeList p1 tail = decodeList p2 tail := by
          refine ih (fun e he => ?_)
          apply hs e
          simp [sxMem, stripSxCons, ht] at he ⊢
          exact Or.inr he
        simp [decodeList, hhead, htail]
    | sym name =>
      intro hs
      simp [decodeList]
    | num _ =>
      intro hs
      simp [decodeList]
    | str _ =>
      intro hs
      simp [decodeList]
  exact key s2 h

/-- Local inhabitation for the `holEl` rendering: HOL's `EL` is total on
`sexp` lists, while `holEl` needs a `Nonempty` instance for the element type. -/
local instance : Nonempty Sexp := ⟨.num 0⟩

/-- Original `sexplist_listsexp_imp`: decoding an encoded list gives back the
images of its elements, index by index. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplist_listsexp_imp"
  (total_function_inhabitants := [α])]
theorem decodeList_listsexp_imp {α : Type} [Nonempty α] (f : Sexp → Option α)
    (l1 : List Sexp) (l2 : List α) (h : decodeList f (listsexp l1) = some l2) :
    ∀ n, n < l1.length → f (holEl n l1) = some (holEl n l2) := by
  intro n hn
  obtain ⟨ys, henc, hmaps⟩ := (decodeList_some f (listsexp l1) l2).mp h
  have hys : l1 = ys := (listsexp_injective l1 ys).mp henc
  subst hys
  have hlen : n < l2.length := by
    have := congrArg List.length hmaps
    simp only [List.length_map] at this
    omega
  have hget : (l1[n]?).map f = (l2[n]?).map some := by
    simpa only [List.getElem?_map] using congrArg (fun l : List (Option α) => l[n]?) hmaps
  rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hlen] at hget
  rw [holEl_eq_getElem n l1 hn, holEl_eq_getElem n l2 hlen]
  simpa using hget

end Flapjack.CakeParser.FromSexp
