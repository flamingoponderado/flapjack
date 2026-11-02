import Flapjack.CakeParser.FromSexp.Control

/-! S-expression list, option and identifier encoder correspondence. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL
open Flapjack.AstHOL

/-- The recursive encoder helper implements the source's `MAP typesexp`. -/
theorem typesexpList_eq_map (ts : List AstT) : typesexpList ts = ts.map typesexp := by
  induction ts with
  | nil => simp [typesexpList]
  | cons t ts ih => simp [typesexpList, ih]

/-- Encoding a proper S-expression list is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "listsexp_11"]
theorem listsexp_injective (left right : List Sexp) : listsexp left = listsexp right ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [listsexp]
  | cons x xs ih =>
    cases right with
    | nil => simp [listsexp]
    | cons y ys =>
      simp only [listsexp] at ih
      simp [listsexp, ih]

/-- Encoding an optional S-expression is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "optsexp_11"]
theorem optsexp_injective (left right : Option Sexp) : optsexp left = optsexp right ↔ left = right := by
  cases left <;> cases right <;> simp [optsexp, listsexp]

/-- Decoding an encoded byte string returns its original mlstring. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSEXSTR_SEXSTR"]
theorem destString_sexstr (bytes : List HolChar) : destString (sexstr bytes) = some (.implode bytes) := by
  simp [destString, sexstr, decode_encode_control]

/-- Decoding an encoded identifier returns the original identifier. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpid_odestSEXSTR_idsexp"]
theorem decodeId_idsexp (id : Ident MlString MlString) : decodeId destString (idsexp id) = some id := by
  induction id with
  | short name =>
    cases name with
    | implode bytes =>
      simp [idsexp, listsexp, decodeId, sexstr, destString, decode_encode_control]
      constructor <;> rfl
  | long name rest ih =>
    cases name with
    | implode bytes =>
      simp [idsexp, listsexp, decodeId, sexstr, destString, decode_encode_control, ih]
      constructor <;> rfl

/-- Pointwise decoding correctness lifts to encoded proper lists. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplist_listsexp_rwt"]
theorem decodeList_listsexp {α : Type} (f : Sexp → Option α) (g : α → Sexp) (xs : List α)
    (h : ∀ x, x ∈ xs → f (g x) = some x) :
    decodeList f (listsexp (xs.map g)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : f (g x) = some x := h x (by simp)
    have ht : ∀ y, y ∈ xs → f (g y) = some y := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih ht
    simp only [listsexp] at hi
    simp [listsexp, decodeList, hx, hi]

/-- Pointwise decoding correctness lifts to encoded options. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpopt_optsexp"]
theorem decodeOption_optsexp {α : Type} (f : Sexp → Option α) (g : α → Sexp) (x : Option α)
    (h : ∀ y, x = some y → f (g y) = x) :
    decodeOption f (optsexp (x.map g)) = some x := by
  cases x with
  | none => rfl
  | some y =>
    have hy := h y rfl
    simp [optsexp, listsexp, decodeOption, stripConstructor, decodeList]
    split <;> simp_all
    all_goals first | rfl | contradiction

/-- Encoding identifiers is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "idsexp_11"]
theorem idsexp_injective (left right : Ident MlString MlString) :
    idsexp left = idsexp right ↔ left = right := by
  constructor
  · intro h
    have decoded := congrArg (decodeId destString) h
    simpa [decodeId_idsexp] using decoded
  · intro h
    subst right
    rfl

mutual
/-- Decoding encoded CakeML type syntax returns the original type. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexptype_typesexp"]
theorem decodeType_typesexp (t : AstT) : decodeType (typesexp t) = some t := by
  cases t with
  | atvar name =>
    cases name with
    | implode bytes => simp (config := { decide := true }) [typesexp, listsexp, decodeType, destString_sexstr]
  | atfun left right =>
    simp (config := { decide := true }) [typesexp, listsexp, decodeType, decodeType_typesexp left, decodeType_typesexp right]
  | attup types =>
    have ih := decodeTypeList_typesexpList types
    simp only [listsexp] at ih
    simp (config := { decide := true }) [typesexp, listsexp, decodeType, ih]
  | atapp types id =>
    have ih := decodeTypeList_typesexpList types
    simp only [listsexp] at ih
    simp (config := { decide := true }) [typesexp, listsexp, decodeType, ih, decodeId_idsexp]
termination_by sizeOf t

/-- The recursive type-list helper round trips each member. -/
theorem decodeTypeList_typesexpList (ts : List AstT) :
    decodeTypeList (listsexp (typesexpList ts)) = some ts := by
  cases ts with
  | nil => simp (config := { decide := true }) [typesexpList, listsexp, decodeTypeList]
  | cons t ts =>
    have ih := decodeTypeList_typesexpList ts
    simp only [listsexp] at ih
    simp [typesexpList, listsexp, decodeTypeList, decodeType_typesexp t, ih]
termination_by sizeOf ts
end

/-- Encoding CakeML type syntax is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "typesexp_11"]
theorem typesexp_injective (left right : AstT) :
    typesexp left = typesexp right ↔ left = right := by
  constructor
  · intro h
    have decoded := congrArg decodeType h
    simpa [decodeType_typesexp] using decoded
  · intro h
    subst right
    rfl

end Flapjack.CakeParser.FromSexp
