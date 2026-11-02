import Flapjack.CakeParser.FromSexp.Control
import Flapjack.CakeParser.FromSexp.Operators

/-! S-expression list, option and identifier encoder correspondence. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL
open Flapjack.AstHOL
open Flapjack.Misc.Location

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

/-- Decoding an encoded literal returns the original literal. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplit_litsexp"]
theorem decodeLiteral_litsexp (l : Lit) : decodeLiteral (litsexp l) = some l := by
  cases l with
  | intLit i =>
    cases i with
    | ofNat n => simp [litsexp, decodeLiteral]
    | negSucc n =>
      simp (config := { decide := true }) [litsexp, listsexp, decodeLiteral,
        stripConstructor, decodeList]
      omega
  | char c => simp (config := { decide := true }) [litsexp, listsexp, decodeLiteral,
      stripConstructor, decodeList, destString_sexstr]
  | strLit s =>
    cases s with
    | implode bytes => simp [litsexp, decodeLiteral, sexstr, destString, decode_encode_control]
  | word8 w => simp (config := { decide := true }) [litsexp, listsexp, decodeLiteral,
      stripConstructor, decodeList, w.isLt]
  | word64 w => simp (config := { decide := true }) [litsexp, listsexp, decodeLiteral,
      stripConstructor, decodeList, w.isLt]
  | float64 w => simp (config := { decide := true }) [litsexp, listsexp, decodeLiteral,
      stripConstructor, decodeList, w.isLt]

/-- Encoding CakeML literals is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "litsexp_11"]
theorem litsexp_injective (left right : Lit) : litsexp left = litsexp right ↔ left = right := by
  constructor
  · intro h
    have decoded := congrArg decodeLiteral h
    simpa [decodeLiteral_litsexp] using decoded
  · intro h
    subst right
    rfl

/-- The recursive pattern encoder helper implements the source's map. -/
theorem patsexpList_eq_map (ps : List Pat) : patsexpList ps = ps.map patsexp := by
  induction ps with
  | nil => simp [patsexpList]
  | cons p ps ih => simp [patsexpList, ih]

mutual
/-- Decoding encoded CakeML pattern syntax returns the original pattern. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexppat_patsexp"]
theorem decodePattern_patsexp (p : Pat) : decodePattern (patsexp p) = some p := by
  cases p with
  | pany => simp (config := { decide := true }) [patsexp, listsexp, decodePattern]
  | pvar name =>
    cases name with
    | implode bytes => simp [patsexp, decodePattern, sexstr, destString, decode_encode_control]
  | plit lit =>
    simp (config := { decide := true }) [patsexp, listsexp, decodePattern, decodeLiteral_litsexp]
  | pcon con pats =>
    have hc : decodeOption (decodeId destString) (optsexp (con.map idsexp)) = some con := by
      apply decodeOption_optsexp
      intro y hy
      subst con
      simp [decodeId_idsexp]
    have ih := decodePatternList_patsexpList pats
    simp only [listsexp] at ih
    simp (config := { decide := true }) [patsexp, listsexp, decodePattern, hc, ih]
  | pref pat =>
    simp (config := { decide := true }) [patsexp, listsexp, decodePattern, decodePattern_patsexp pat]
  | pas pat name =>
    cases name with
    | implode bytes =>
      simp (config := { decide := true }) [patsexp, listsexp, decodePattern,
        decodePattern_patsexp pat, destString_sexstr]
  | ptannot pat type =>
    simp (config := { decide := true }) [patsexp, listsexp, decodePattern,
      decodePattern_patsexp pat, decodeType_typesexp]
termination_by sizeOf p

/-- The recursive pattern-list helper round trips each member. -/
theorem decodePatternList_patsexpList (ps : List Pat) :
    decodePatternList (listsexp (patsexpList ps)) = some ps := by
  cases ps with
  | nil => simp (config := { decide := true }) [patsexpList, listsexp, decodePatternList]
  | cons p ps =>
    have ih := decodePatternList_patsexpList ps
    simp only [listsexp] at ih
    simp [patsexpList, listsexp, decodePatternList, decodePattern_patsexp p, ih]
termination_by sizeOf ps
end

/-- Encoding CakeML patterns is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "patsexp_11"]
theorem patsexp_injective (left right : Pat) : patsexp left = patsexp right ↔ left = right := by
  constructor
  · intro h
    have decoded := congrArg decodePattern h
    simpa [decodePattern_patsexp] using decoded
  · intro h
    subst right
    rfl

/-- Source location points round trip through S-expressions. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplocpt_locnsexp"]
theorem decodeLocPoint_locnsexp (point : Locn) : decodeLocPoint (locnsexp point) = some point := by
  cases point <;> simp (config := { decide := true }) [locnsexp, decodeLocPoint, listsexp, decodeList]

/-- Source locations round trip through S-expressions. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplocn_locnsexp"]
theorem decodeLoc_locssexp (loc : Locs) : decodeLoc (locssexp loc) = some loc := by
  cases loc with
  | locs a b =>
    simp (config := { decide := true }) [locssexp, listsexp, decodeLoc, decodeList,
      decodeLocPoint_locnsexp]

/-- Logical operators round trip through S-expressions. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplog_logsexp"]
theorem decodeLog_logsexp (op : Lop) : decodeLog (logsexp op) = some op := by
  cases op <;> decide

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locnsexp_11"]
theorem locnsexp_injective (a b : Locn) : locnsexp a = locnsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeLocPoint h
    simpa [decodeLocPoint_locnsexp] using decoded
  · rintro rfl
    rfl

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locssexp_11"]
theorem locssexp_injective (a b : Locs) : locssexp a = locssexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeLoc h
    simpa [decodeLoc_locssexp] using decoded
  · rintro rfl
    rfl

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "logsexp_11"]
theorem logsexp_injective (a b : Lop) : logsexp a = logsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeLog h
    simpa [decodeLog_logsexp] using decoded
  · rintro rfl
    rfl

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "arithsexp_sexparith"]
theorem decodeArith_arithsexp (op : Arith) : decodeArith (arithsexp op) = some op := by
  cases op <;> decide

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpprim_type_testsexp"]
theorem decodePrimType_primTypesexp (type : PrimType) :
    decodePrimType (primTypesexp type) = some type := by
  cases type with
  | wordT width => cases width <;> decide
  | boolT | intT | charT | strT | float64T => decide

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexptest_testsexp"]
theorem decodeTest_testsexp (test : Test) : decodeTest (testsexp test) = some test := by
  cases test with
  | equal => decide
  | compare op | altCompare op => cases op <;> decide

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "arithsexp_11"]
theorem arithsexp_injective (a b : Arith) : arithsexp a = arithsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeArith h
    simpa [decodeArith_arithsexp] using decoded
  · rintro rfl
    rfl

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "prim_typesexp_11"]
theorem primTypesexp_injective (a b : PrimType) : primTypesexp a = primTypesexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodePrimType h
    simpa [decodePrimType_primTypesexp] using decoded
  · rintro rfl
    rfl

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "testsexp_11"]
theorem testsexp_injective (a b : Test) : testsexp a = testsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeTest h
    simpa [decodeTest_testsexp] using decoded
  · rintro rfl
    rfl

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpop_opsexp"]
theorem decodeOp_opsexp (op : Op) : decodeOp (opsexp op) = some op := by
  cases op <;> try decide
  case arith a p =>
    simp (config := { decide := true }) [opsexp, opSym, decodeOp, decodeArith_arithsexp, decodePrimType_primTypesexp]
  case fromTo a b =>
    simp (config := { decide := true }) [opsexp, opSym, decodeOp, decodePrimType_primTypesexp]
  case test t p =>
    simp (config := { decide := true }) [opsexp, opSym, decodeOp, decodeTest_testsexp, decodePrimType_primTypesexp]
  case shift width shift n =>
    cases width <;> cases shift <;> simp (config := { decide := true }) [opsexp, opSym, opShiftName, decodeOp]
    all_goals rfl
  case ffi s =>
    cases s with
    | implode bytes => simp (config := { decide := true }) [opsexp, opSym, decodeOp, sexstr, destString, decode_encode_control]
  case thunkOp thunk =>
    cases thunk with
    | forceThunk => decide
    | allocThunk mode => cases mode <;> decide
    | updateThunk mode => cases mode <;> decide

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "opsexp_11"]
theorem opsexp_injective (a b : Op) : opsexp a = opsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeOp h
    simpa [decodeOp_opsexp] using decoded
  · rintro rfl
    rfl

end Flapjack.CakeParser.FromSexp
