import Flapjack.CakeParser.FromSexp.Control.Canonical
import Flapjack.CakeParser.FromSexp.Operators
import Flapjack.CakeParser.FromSexp.Ast

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

/-- Successful string decoding accepts exactly the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "odestSEXSTR_SOME"]
theorem destString_some (s : Sexp) (y : MlString) :
    (destString s = some y ↔ s = sexstr y.explode) ∧
    (some y = destString s ↔ s = sexstr y.explode) := by
  have forward : destString s = some y → s = sexstr y.explode := by
    intro h
    cases s with
    | str bytes =>
      cases hd : decodeControl bytes with
      | none => simp [destString, hd] at h
      | some decoded =>
        simp [destString, hd] at h
        subst y
        simp [sexstr, encode_decode_control bytes decoded hd]
    | sym _ | num _ | cons _ _ => simp [destString] at h
  have backward : s = sexstr y.explode → destString s = some y := by
    intro h
    subst s
    cases y with
    | implode bytes => exact destString_sexstr bytes
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

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

/-- A successfully decoded identifier has its canonical S-expression shape. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "idsexp_sexpid_odestSEXSTR"]
theorem decodeId_some (id : Ident MlString MlString) (s : Sexp) :
    decodeId destString s = some id ↔ s = idsexp id := by
  constructor
  · intro h
    induction s using decodeId.induct generalizing id with
    | case1 name value terminator condition =>
      have eqs : name = (ofString "Short").explode ∧ terminator = (ofString "nil").explode := by
        simp only [Bool.and_eq_true, beq_iff_eq] at condition
        constructor
        · convert condition.1 using 1
          rfl
        · convert condition.2 using 1
          rfl
      cases hv : destString value with
      | none => simp [decodeId, condition, hv] at h
      | some v =>
        simp [decodeId, condition, hv] at h
        subst id
        have encoded := (destString_some value v).1.mp hv
        rcases eqs with ⟨rfl, rfl⟩
        simp [idsexp, listsexp, encoded]
        constructor <;> rfl
    | case2 name value terminator condition => simp [decodeId, condition] at h
    | case3 name moduleName rest terminator condition ih =>
      have eqs : name = (ofString "Long").explode ∧ terminator = (ofString "nil").explode := by
        simp only [Bool.and_eq_true, beq_iff_eq] at condition
        constructor
        · convert condition.1 using 1
          rfl
        · convert condition.2 using 1
          rfl
      cases hv : destString moduleName with
      | none => simp [decodeId, condition, hv] at h
      | some v =>
        cases hr : decodeId destString rest with
        | none => simp [decodeId, condition, hv, hr] at h
        | some tail =>
          simp [decodeId, condition, hv, hr] at h
          subst id
          have encoded := (destString_some moduleName v).1.mp hv
          have encodedRest := ih tail hr
          rcases eqs with ⟨rfl, rfl⟩
          simp [idsexp, listsexp, encoded, encodedRest]
          constructor <;> rfl
    | case4 name moduleName rest terminator condition => simp [decodeId, condition] at h
    | case5 s hshort hlong =>
      rw [decodeId.eq_def] at h
      split at h <;> simp_all
  · intro h
    subst s
    exact decodeId_idsexp id

/-- Identifier canonicality in both orientations of option equality. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "idsexp_sexpid_odestSEXSTR'"]
theorem decodeId_some_both (s : Sexp) (id : Ident MlString MlString) :
    (decodeId destString s = some id ↔ s = idsexp id) ∧
    (some id = decodeId destString s ↔ s = idsexp id) := by
  refine ⟨decodeId_some id s, ?_⟩
  constructor
  · intro h
    exact (decodeId_some id s).mp h.symm
  · intro h
    exact ((decodeId_some id s).mpr h).symm

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

/-- Successful list decoding identifies a proper encoded list and its elements. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplist_SOME"]
theorem decodeList_some {α : Type} (f : Sexp → Option α) (s : Sexp) (xs : List α) :
    decodeList f s = some xs ↔ ∃ ys, s = listsexp ys ∧ ys.map f = xs.map some := by
  constructor
  · intro h
    induction s generalizing xs with
    | sym name =>
      simp only [decodeList] at h
      split at h
      next heq =>
        simp only [Option.some.injEq] at h
        subst xs
        refine ⟨[], ?_, rfl⟩
        simp only [beq_iff_eq] at heq
        subst name
        rfl
      next => contradiction
    | num _ | str _ => simp [decodeList] at h
    | cons head tail _ ih =>
      cases hh : f head with
      | none => simp [decodeList, hh] at h
      | some x =>
        cases ht : decodeList f tail with
        | none => simp [decodeList, hh, ht] at h
        | some rest =>
          simp [decodeList, hh, ht] at h
          subst xs
          obtain ⟨ys, rfl, maps⟩ := ih rest ht
          refine ⟨head :: ys, ?_, ?_⟩
          · simp [listsexp]
          · simp [hh, maps]
  · rintro ⟨ys, rfl, maps⟩
    induction ys generalizing xs with
    | nil =>
      cases xs with
      | nil => rfl
      | cons _ _ => simp at maps
    | cons y ys ih =>
      cases xs with
      | nil => simp at maps
      | cons x xs =>
        simp only [List.map_cons, List.cons.injEq] at maps
        have tail := ih xs maps.2
        simp only [listsexp] at tail
        simp [listsexp, decodeList, maps.1, tail]

/-- Successful pair decoding identifies the encoded components. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexppair_SOME"]
theorem decodePair_some {α β : Type} (f : Sexp → Option α) (g : Sexp → Option β)
    (s : Sexp) (p : α × β) : decodePair f g s = some p ↔
      ∃ x y a b, f x = some a ∧ g y = some b ∧ s = .cons x y ∧ p = (a, b) := by
  cases s with
  | sym _ | num _ | str _ => simp [decodePair]
  | cons x y =>
    cases hf : f x <;> cases hg : g y <;> simp [decodePair, hf, hg, eq_comm]

/-- The identity list decoder recognizes exactly proper S-expression lists.
This specializes `sexplist_SOME` for Flapjack's constructor helper. -/
theorem decodeList_some_identity (s : Sexp) (xs : List Sexp) :
    decodeList some s = some xs ↔ s = listsexp xs := by
  constructor
  · intro h
    obtain ⟨ys, encoded, maps⟩ := (decodeList_some some s xs).mp h
    have same : ys = xs := (List.map_inj_right (fun _ _ => Option.some.inj)).mp maps
    simpa [same] using encoded
  · intro h
    subst s
    simpa using decodeList_listsexp some id xs (by simp)

/-- A stripped constructor has precisely a symbol followed by a proper list.
This describes Flapjack's `stripConstructor` helper. -/
theorem stripConstructor_some (s : Sexp) (name : List HolChar) (args : List Sexp) :
    stripConstructor s = some (name, args) ↔ s = .cons (.sym name) (listsexp args) := by
  cases s with
  | sym _ | num _ | str _ => simp [stripConstructor]
  | cons head tail =>
    cases head with
    | sym tag =>
      cases ht : decodeList some tail with
      | none =>
        have hn : ∀ xs, tail ≠ listsexp xs := by
          intro xs heq
          have := (decodeList_some_identity tail xs).mpr heq
          simp [ht] at this
        simp [stripConstructor, ht, hn]
      | some values =>
        have heq : tail = listsexp values := (decodeList_some_identity tail values).mp ht
        simp only [stripConstructor, ht, Sexp.cons.injEq, Sexp.sym.injEq]
        rw [heq, listsexp_injective]
        simp
    | num _ | str _ | cons _ _ => simp [stripConstructor]

/-- Successful option decoding identifies the original option encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpopt_SOME"]
theorem decodeOption_some {α : Type} (f : Sexp → Option α) (s : Sexp) (opt : Option α) :
    decodeOption f s = some opt ↔
      (opt = none ∧ s = .sym ((ofString "NONE").explode)) ∨
      ∃ x s0, opt = some x ∧ f s0 = some x ∧
        s = listsexp [.sym ((ofString "SOME").explode), s0] := by
  cases s with
  | sym name =>
    simp [decodeOption, listsexp]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.symm, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1.symm⟩
  | num _ | str _ => simp [decodeOption, stripConstructor, listsexp]
  | cons head tail =>
    have encoded (s0 : Sexp) :
        Sexp.cons head tail = listsexp [.sym ((ofString "SOME").explode), s0] ↔
          stripConstructor (.cons head tail) = some (((ofString "SOME").explode), [s0]) := by
      rw [stripConstructor_some]
      rfl
    simp only [encoded]
    cases h : stripConstructor (.cons head tail) with
    | none => simp [decodeOption, h]
    | some pair =>
      rcases pair with ⟨name, args⟩
      cases args with
      | nil => simp [decodeOption, h]
      | cons value rest =>
        cases rest with
        | nil =>
          simp [decodeOption, h]
          constructor
          · rintro ⟨hn, x, hf, ho⟩
            exact ⟨x, ho.symm, hf, hn⟩
          · rintro ⟨x, ho, hf, hn⟩
            exact ⟨hn, x, hf, ho.symm⟩
        | cons another rest => simp [decodeOption, h]

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

/-- Successful type decoding yields the source-shaped encoding. This is the
reverse direction of `typesexp_sexptype` over the executed decoder. -/
theorem decodeType_canonical (s : Sexp) : ∀ t, decodeType s = some t → typesexp t = s := by
  induction s using decodeType.induct
      (motive2 := fun x => ∀ ts, decodeTypeList x = some ts → listsexp (ts.map typesexp) = x) with
  | case1 name value terminator hterm =>
    intro t h
    simp [decodeType, hterm] at h
  | case2 name value terminator hterm hname =>
    intro t h
    cases hv : destString value with
    | none => simp [decodeType, hterm, hname, hv] at h
    | some v =>
      simp [decodeType, hterm, hname, hv] at h
      subst t
      have enc := (destString_some value v).1.mp hv
      simp only [beq_iff_eq] at hname
      simp only [bne_iff_ne, not_not] at hterm
      simp [typesexp, listsexp, enc, hname, hterm]
      constructor <;> rfl
  | case3 name value terminator hterm hnot hname ih =>
    intro t h
    cases hv : decodeTypeList value with
    | none => simp [decodeType, hterm, hnot, hname, hv] at h
    | some ts =>
      simp [decodeType, hterm, hnot, hname, hv] at h
      subst t
      have enc := ih ts hv
      simp only [listsexp] at enc
      simp only [beq_iff_eq] at hname
      simp only [bne_iff_ne, not_not] at hterm
      simp [typesexp, typesexpList_eq_map, listsexp, enc, hname, hterm]
      constructor <;> rfl
  | case4 name value terminator hterm hnot hname =>
    intro t h
    simp [decodeType, hterm, hnot, hname] at h
  | case5 name a b terminator hterm =>
    intro t h
    simp [decodeType, hterm] at h
  | case6 name a b terminator hterm hname iha ihb =>
    intro t h
    cases ha : decodeType a with
    | none => simp [decodeType, hterm, hname, ha] at h
    | some ta =>
      cases hb : decodeType b with
      | none => simp [decodeType, hterm, hname, ha, hb] at h
      | some tb =>
        simp [decodeType, hterm, hname, ha, hb] at h
        subst t
        have ea := iha ta ha
        have eb := ihb tb hb
        simp only [beq_iff_eq] at hname
        simp only [bne_iff_ne, not_not] at hterm
        simp [typesexp, listsexp, ea, eb, hname, hterm]
        constructor <;> rfl
  | case7 name a b terminator hterm hnot hname ih =>
    intro t h
    cases ha : decodeTypeList a with
    | none => simp [decodeType, hterm, hnot, hname, ha] at h
    | some ts =>
      cases hb : decodeId destString b with
      | none => simp [decodeType, hterm, hnot, hname, ha, hb] at h
      | some id =>
        simp [decodeType, hterm, hnot, hname, ha, hb] at h
        subst t
        have ea := ih ts ha
        have eb := (decodeId_some id b).mp hb
        simp only [listsexp] at ea
        simp only [beq_iff_eq] at hname
        simp only [bne_iff_ne, not_not] at hterm
        simp [typesexp, typesexpList_eq_map, listsexp, ea, eb, hname, hterm]
        constructor <;> rfl
  | case8 name a b terminator hterm hnot hname =>
    intro t h
    simp [decodeType, hterm, hnot, hname] at h
  | case9 x h1 h2 =>
    intro t h
    rw [decodeType.eq_def] at h
    split at h <;> simp_all
  | case10 head tail ihh iht ts h =>
    cases hh : decodeType head with
    | none => simp [decodeTypeList, hh] at h
    | some t =>
      cases ht : decodeTypeList tail with
      | none => simp [decodeTypeList, hh, ht] at h
      | some rest =>
        simp [decodeTypeList, hh, ht] at h
        subst ts
        have eh := ihh t hh
        have et := iht rest ht
        simp only [listsexp] at et
        simp [listsexp, eh, et]
  | case11 name hn ts h =>
    simp [decodeTypeList, hn] at h
    subst ts
    simp only [beq_iff_eq] at hn
    simp [listsexp, hn]
    rfl
  | case12 name hn ts h =>
    simp [decodeTypeList, hn] at h
  | case13 x h1 h2 ts h =>
    rw [decodeTypeList.eq_def] at h
    split at h <;> simp_all

/-- Type decoding succeeds exactly on the canonical encoding, in both
orientations of option equality. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "typesexp_sexptype"]
theorem decodeType_some (s : Sexp) (t : AstT) :
    (decodeType s = some t ↔ typesexp t = s) ∧
    (some t = decodeType s ↔ typesexp t = s) := by
  have forward : decodeType s = some t → typesexp t = s := decodeType_canonical s t
  have backward : typesexp t = s → decodeType s = some t := by
    intro h
    subst s
    exact decodeType_typesexp t
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

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

/-- The string helper used in expression encoding is reversed by `destString`. -/
theorem destString_expsexpString (s : MlString) : destString (expsexpString s) = some s := by
  cases s with
  | implode bytes => simp [expsexpString, destString_sexstr]

/-- The expression-list encoder helper is the source's map. -/
theorem expsexpList_eq_map (es : List Exp) : expsexpList es = es.map expsexp := by
  induction es with
  | nil => simp [expsexpList]
  | cons e es ih => simp [expsexpList, ih]

/-- The clause encoder helper is the source's map over pattern-expression pairs. -/
theorem expsexpClauses_eq_map (clauses : List (Pat × Exp)) :
    expsexpClauses clauses = clauses.map (fun (p, e) => .cons (patsexp p) (expsexp e)) := by
  induction clauses with
  | nil => simp [expsexpClauses]
  | cons clause clauses ih =>
    rcases clause with ⟨p, e⟩
    simp [expsexpClauses, ih]

/-- The recursive-function encoder helper is the source's map over triples. -/
theorem expsexpFuns_eq_map (fs : List (VarN × VarN × Exp)) :
    expsexpFuns fs = fs.map (fun (f, x, e) =>
      .cons (expsexpString f) (.cons (expsexpString x) (expsexp e))) := by
  induction fs with
  | nil => simp [expsexpFuns]
  | cons f fs ih =>
    rcases f with ⟨name, arg, body⟩
    simp [expsexpFuns, ih]

mutual
/-- Decoding encoded CakeML expressions returns the original expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpexp_expsexp"]
theorem decodeExp_expsexp (e : Exp) : decodeExp (expsexp e) = some e := by
  cases e with
  | raise e =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, decodeExp_expsexp e]
  | handle e clauses =>
    have ih := decodeClauses_expsexpClauses clauses
    simp only [listsexp] at ih
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, decodeExp_expsexp e, ih]
  | lit l =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, decodeLiteral_litsexp]
  | con id es =>
    have hid : decodeOption (decodeId destString) (optsexp (id.map idsexp)) = some id := by
      apply decodeOption_optsexp
      intro y hy
      subst id
      simp [decodeId_idsexp]
    have ih := decodeExpList_expsexpList es
    simp only [listsexp] at ih
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, hid, ih]
  | var id =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, decodeId_idsexp]
  | fn name body =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp,
      destString_expsexpString, decodeExp_expsexp body]
  | app op es =>
    have ih := decodeExpList_expsexpList es
    simp only [listsexp] at ih
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, decodeOp_opsexp, ih]
  | log op a b =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp,
      decodeLog_logsexp, decodeExp_expsexp a, decodeExp_expsexp b]
  | if_ a b c =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp,
      decodeExp_expsexp a, decodeExp_expsexp b, decodeExp_expsexp c]
  | mat e clauses =>
    have ih := decodeClauses_expsexpClauses clauses
    simp only [listsexp] at ih
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, decodeExp_expsexp e, ih]
  | let_ name a b =>
    have hn : decodeOption destString (optsexp (name.map expsexpString)) = some name := by
      apply decodeOption_optsexp
      intro y hy
      subst name
      simp [destString_expsexpString]
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp,
      hn, decodeExp_expsexp a, decodeExp_expsexp b]
  | letrec fs e =>
    have ih := decodeFunctions_expsexpFuns fs
    simp only [listsexp] at ih
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp, ih, decodeExp_expsexp e]
  | tannot e t =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp,
      decodeExp_expsexp e, decodeType_typesexp]
  | lannot e l =>
    simp (config := { decide := true }) [expsexp, expsexpNode, listsexp, decodeExp,
      decodeExp_expsexp e, decodeLoc_locssexp]
termination_by sizeOf e

/-- Encoded expression lists round trip. -/
theorem decodeExpList_expsexpList (es : List Exp) :
    decodeExpList (listsexp (expsexpList es)) = some es := by
  cases es with
  | nil => simp (config := { decide := true }) [expsexpList, listsexp, decodeExpList]
  | cons e es =>
    have ih := decodeExpList_expsexpList es
    simp only [listsexp] at ih
    simp [expsexpList, listsexp, decodeExpList, decodeExp_expsexp e, ih]
termination_by sizeOf es

/-- Encoded pattern-expression clauses round trip. -/
theorem decodeClauses_expsexpClauses (clauses : List (Pat × Exp)) :
    decodeClauses (listsexp (expsexpClauses clauses)) = some clauses := by
  cases clauses with
  | nil => simp (config := { decide := true }) [expsexpClauses, listsexp, decodeClauses]
  | cons clause clauses =>
    rcases clause with ⟨p, e⟩
    have ih := decodeClauses_expsexpClauses clauses
    simp only [listsexp] at ih
    simp [expsexpClauses, listsexp, decodeClauses, decodePattern_patsexp, decodeExp_expsexp e, ih]
termination_by sizeOf clauses

/-- Encoded recursive-function lists round trip. -/
theorem decodeFunctions_expsexpFuns (fs : List (VarN × VarN × Exp)) :
    decodeFunctions (listsexp (expsexpFuns fs)) = some fs := by
  cases fs with
  | nil => simp (config := { decide := true }) [expsexpFuns, listsexp, decodeFunctions]
  | cons f fs =>
    rcases f with ⟨name, arg, body⟩
    have ih := decodeFunctions_expsexpFuns fs
    simp only [listsexp] at ih
    simp [expsexpFuns, listsexp, decodeFunctions, destString_expsexpString, decodeExp_expsexp body, ih]
termination_by sizeOf fs
end

/-- Expression encoding is injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "expsexp_11"]
theorem expsexp_injective (left right : Exp) (h : expsexp left = expsexp right) : left = right := by
  have decoded := congrArg decodeExp h
  simpa [decodeExp_expsexp] using decoded

/-- Lists of encoded mlstrings round trip through the generic list decoder. -/
theorem decodeStringList (xs : List MlString) :
    decodeList destString (listsexp (xs.map expsexpString)) = some xs := by
  apply decodeList_listsexp
  intro x _
  exact destString_expsexpString x

/-- Lists of encoded types round trip through the type-list decoder. -/
theorem decodeTypeList_map (xs : List AstT) :
    decodeTypeList (listsexp (xs.map typesexp)) = some xs := by
  rw [← typesexpList_eq_map]
  exact decodeTypeList_typesexpList xs

/-- Datatype definition constructor lists round trip. -/
theorem decodeTypeDefConstructors (xs : List (MlString × List AstT)) :
    decodeList (decodePair destString decodeTypeList)
      (listsexp (xs.map (fun (name, ts) => .cons (expsexpString name) (listsexp (ts.map typesexp))))) = some xs := by
  apply decodeList_listsexp
  intro x _
  rcases x with ⟨name, ts⟩
  simp [decodePair, destString_expsexpString, decodeTypeList_map]

/-- Encoded datatype definitions round trip. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexptype_def_type_defsexp"]
theorem decodeTypeDef_typeDefsexp (td : TypeDef) : decodeTypeDef (typeDefsexp td) = some td := by
  unfold decodeTypeDef typeDefsexp
  apply decodeList_listsexp
  intro x _
  rcases x with ⟨vs, name, cs⟩
  simp [decodePair, decodeStringList, destString_expsexpString, decodeTypeDefConstructors]

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "type_defsexp_11"]
theorem typeDefsexp_injective (a b : TypeDef) : typeDefsexp a = typeDefsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeTypeDef h
    simpa [decodeTypeDef_typeDefsexp] using decoded
  · rintro rfl
    rfl

/-- The declaration encoder helper is the source's map. -/
theorem decsexpList_eq_map (ds : List Dec) : decsexpList ds = ds.map decsexp := by
  induction ds with
  | nil => simp [decsexpList]
  | cons d ds ih => simp [decsexpList, ih]

mutual
/-- Decoding encoded declarations returns the original declaration. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpdec_decsexp"]
theorem decodeDec_decsexp (d : Dec) : decodeDec (decsexp d) = some d := by
  cases d with
  | dlet l p e =>
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      decodeLoc_locssexp, decodePattern_patsexp, decodeExp_expsexp]
  | dletrec l fs =>
    have ih := decodeFunctions_expsexpFuns fs
    simp only [listsexp] at ih
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      decodeLoc_locssexp, ih]
  | dtype l td =>
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      decodeLoc_locssexp, decodeTypeDef_typeDefsexp]
  | dtabbrev l ns name type =>
    have ih := decodeStringList ns
    simp only [listsexp] at ih
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      decodeLoc_locssexp, destString_expsexpString, decodeType_typesexp, ih]
  | dexn l name ts =>
    have ih := decodeTypeList_map ts
    simp only [listsexp] at ih
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      decodeLoc_locssexp, destString_expsexpString, ih]
  | dmod name ds =>
    have ih := decodeDecList_decsexpList ds
    simp only [listsexp] at ih
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      destString_expsexpString, ih]
  | dlocal a b =>
    have ia := decodeDecList_decsexpList a
    have ib := decodeDecList_decsexpList b
    simp only [listsexp] at ia ib
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec, ia, ib]
  | denv name =>
    simp (config := { decide := true }) [decsexp, expsexpNode, listsexp, decodeDec,
      destString_expsexpString]
termination_by sizeOf d

/-- Encoded declaration lists round trip. -/
theorem decodeDecList_decsexpList (ds : List Dec) :
    decodeDecList (listsexp (decsexpList ds)) = some ds := by
  cases ds with
  | nil => simp (config := { decide := true }) [decsexpList, listsexp, decodeDecList]
  | cons d ds =>
    have ih := decodeDecList_decsexpList ds
    simp only [listsexp] at ih
    simp [decsexpList, listsexp, decodeDecList, decodeDec_decsexp d, ih]
termination_by sizeOf ds
end

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decsexp_11"]
theorem decsexp_injective (a b : Dec) : decsexp a = decsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeDec h
    simpa [decodeDec_decsexp] using decoded
  · rintro rfl
    rfl

/-- The executable's whole-program encoder round trips through its
declaration-list decoder. This assembles the HOL component lemmas for the
Flapjack driver; it has no separate HOL declaration. -/
theorem decodeProgram_toSexp (ds : List Dec) :
    decodeDecList (Flapjack.CakeParser.ToSexp.program ds) = some ds := by
  unfold Flapjack.CakeParser.ToSexp.program
  rw [← decsexpList_eq_map]
  exact decodeDecList_decsexpList ds

end Flapjack.CakeParser.FromSexp
