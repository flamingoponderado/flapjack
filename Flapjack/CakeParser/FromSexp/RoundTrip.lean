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

/-- A list decoder inherits canonicality from its element decoder. This is
Flapjack infrastructure assembled from the source list inverse theorem. -/
theorem decodeList_canonical {α : Type} (f : Sexp → Option α) (g : α → Sexp)
    (element : ∀ s x, f s = some x → g x = s)
    (s : Sexp) (xs : List α) (h : decodeList f s = some xs) :
    listsexp (xs.map g) = s := by
  obtain ⟨ys, rfl, maps⟩ := (decodeList_some f s xs).mp h
  clear h
  have same : xs.map g = ys := by
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
        simp [element y x maps.1, ih xs maps.2]
  rw [same]

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

/-- Successful decoding of an optional identifier yields its canonical
encoding. This specializes the source option and identifier inverse lemmas. -/
theorem decodeIdOption_canonical (s : Sexp) (id : Option (Ident MlString MlString))
    (h : decodeOption (decodeId destString) s = some id) : optsexp (id.map idsexp) = s := by
  rcases (decodeOption_some (decodeId destString) s id).mp h with ⟨rfl, rfl⟩ | ⟨x, s0, rfl, hx, hs⟩
  · rfl
  · have eq := (decodeId_some x s0).mp hx
    subst s0
    rw [hs]
    simp [optsexp, listsexp]
    rfl

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

/-- The executed type-list decoder accepts only canonical encoded lists. -/
theorem decodeTypeList_canonical (s : Sexp) (ts : List AstT)
    (h : decodeTypeList s = some ts) : listsexp (ts.map typesexp) = s := by
  induction s generalizing ts with
  | sym name =>
    simp only [decodeTypeList] at h
    split at h
    next hn =>
      simp at h
      subst ts
      simp only [beq_iff_eq] at hn
      simp [listsexp, hn]
      rfl
    next => contradiction
  | num _ | str _ => simp [decodeTypeList] at h
  | cons head tail _ ih =>
    cases hh : decodeType head with
    | none => simp [decodeTypeList, hh] at h
    | some t =>
      cases ht : decodeTypeList tail with
      | none => simp [decodeTypeList, hh, ht] at h
      | some rest =>
        simp [decodeTypeList, hh, ht] at h
        subst ts
        have eh := decodeType_canonical head t hh
        have et := ih rest ht
        simp only [listsexp] at et
        simp [listsexp, eh, et]

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

/-- Successful literal decoding yields the source-shaped encoding. This is
the reverse direction of `litsexp_sexplit` for the executed decoder. -/
theorem decodeLiteral_canonical (s : Sexp) (lit : Lit) (h : decodeLiteral s = some lit) : litsexp lit = s := by
  cases s with
  | num n =>
    simp [decodeLiteral] at h
    subst lit
    rfl
  | str bytes =>
    cases hs : destString (.str bytes) with
    | none => simp [decodeLiteral, hs] at h
    | some value =>
      simp [decodeLiteral, hs] at h
      subst lit
      simpa [litsexp] using ((destString_some (.str bytes) value).1.mp hs).symm
  | sym name => simp [decodeLiteral, stripConstructor] at h
  | cons head tail =>
    cases hs : stripConstructor (.cons head tail) with
    | none => simp [decodeLiteral, hs] at h
    | some pair =>
      rcases pair with ⟨name, args⟩
      have shape := (stripConstructor_some _ _ _).mp hs
      cases args with
      | nil => simp [decodeLiteral, hs] at h
      | cons arg rest =>
        cases rest with
        | cons a r => simp [decodeLiteral, hs] at h
        | nil =>
          simp only [decodeLiteral, hs] at h
          dsimp at h
          split at h
          next neg =>
            cases arg with
            | num n =>
              cases n with
              | zero => simp at h
              | succ n =>
                simp at h
                subst lit
                simp only [beq_iff_eq] at neg
                rw [shape]
                have ineg : -1 + -(n : Int) = Int.negSucc n := by omega
                rw [ineg]
                simp [litsexp, listsexp, neg]
                rfl
            | sym _ | str _ | cons _ _ => simp at h
          next notNeg =>
            split at h
            next charName =>
              cases hd : destString arg with
              | none => simp [hd] at h
              | some val =>
                cases val with
                | implode bytes =>
                  cases bytes with
                  | nil => simp [hd] at h
                  | cons c cs =>
                    cases cs with
                    | nil =>
                      simp [hd] at h
                      subst lit
                      have eqArg := (destString_some arg (.implode [c])).1.mp hd
                      simp only [beq_iff_eq] at charName
                      rw [shape]
                      simp [litsexp, listsexp, charName, eqArg]
                      rfl
                    | cons d ds => simp [hd] at h
            next notChar =>
              cases arg with
              | num n =>
                dsimp at h
                split at h
                next word8 =>
                  simp at h
                  subst lit
                  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at word8
                  rw [shape]
                  simp [litsexp, listsexp, word8.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt word8.2]
                  rfl
                next notWord8 =>
                  split at h
                  next word64 =>
                    simp at h
                    subst lit
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at word64
                    rw [shape]
                    simp [litsexp, listsexp, word64.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt word64.2]
                    rfl
                  next notWord64 =>
                    split at h
                    next float64 =>
                      simp at h
                      subst lit
                      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at float64
                      rw [shape]
                      simp [litsexp, listsexp, float64.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt float64.2]
                      rfl
                    next _ => simp at h
              | sym _ | str _ | cons _ _ => simp at h

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

/-- Literal decoding succeeds exactly on the canonical encoding, in both
orientations of option equality. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "litsexp_sexplit"]
theorem decodeLiteral_some (s : Sexp) (lit : Lit) :
    (decodeLiteral s = some lit ↔ litsexp lit = s) ∧
    (some lit = decodeLiteral s ↔ litsexp lit = s) := by
  have forward : decodeLiteral s = some lit → litsexp lit = s := decodeLiteral_canonical s lit
  have backward : litsexp lit = s → decodeLiteral s = some lit := by
    intro h
    subst s
    exact decodeLiteral_litsexp lit
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

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

/-- Every successfully decoded pattern has its canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "patsexp_sexppat0"]
theorem decodePattern_canonical (s : Sexp) : ∀ p, decodePattern s = some p → patsexp p = s := by
  induction s using decodePattern.induct
      (motive2 := fun x => ∀ ps, decodePatternList x = some ps → listsexp (ps.map patsexp) = x) with
  | case1 bytes =>
    intro p h
    cases hd : destString (.str bytes) with
    | none => simp [decodePattern, hd] at h
    | some name =>
      simp [decodePattern, hd] at h
      subst p
      have enc := (destString_some (.str bytes) name).1.mp hd
      simpa [patsexp] using enc.symm
  | case2 name terminator hn =>
    intro p h
    simp [decodePattern, hn] at h
    subst p
    simp only [Bool.and_eq_true, beq_iff_eq] at hn
    simp [patsexp, listsexp, hn.1, hn.2]
    constructor <;> rfl
  | case3 name terminator hn =>
    intro p h
    simp [decodePattern, hn] at h
  | case4 name a terminator ht =>
    intro p h
    simp [decodePattern, ht] at h
  | case5 name a terminator ht hn =>
    intro p h
    cases ha : decodeLiteral a with
    | none => simp [decodePattern, ht, hn, ha] at h
    | some lit =>
      simp [decodePattern, ht, hn, ha] at h
      subst p
      have ea := (decodeLiteral_some a lit).1.mp ha
      simp only [beq_iff_eq] at hn
      simp only [bne_iff_ne, not_not] at ht
      simp [patsexp, listsexp, ea, hn, ht]
      constructor <;> rfl
  | case6 name a terminator ht hnot hn ih =>
    intro p h
    cases ha : decodePattern a with
    | none => simp [decodePattern, ht, hnot, hn, ha] at h
    | some pat =>
      simp [decodePattern, ht, hnot, hn, ha] at h
      subst p
      have ea := ih pat ha
      simp only [beq_iff_eq] at hn
      simp only [bne_iff_ne, not_not] at ht
      simp [patsexp, listsexp, ea, hn, ht]
      constructor <;> rfl
  | case7 name a terminator ht hnot hn =>
    intro p h
    simp [decodePattern, ht, hnot, hn] at h
  | case8 name a b terminator ht =>
    intro p h
    simp [decodePattern, ht] at h
  | case9 name a b terminator ht hn ih =>
    intro p h
    cases ha : decodeOption (decodeId destString) a with
    | none => simp [decodePattern, ht, hn, ha] at h
    | some id =>
      cases hb : decodePatternList b with
      | none => simp [decodePattern, ht, hn, ha, hb] at h
      | some ps =>
        simp [decodePattern, ht, hn, ha, hb] at h
        subst p
        have ea := decodeIdOption_canonical a id ha
        have eb := ih ps hb
        simp only [listsexp] at eb
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [patsexp, patsexpList_eq_map, listsexp, ea, eb, hn, ht]
        constructor <;> rfl
  | case10 name a b terminator ht hnot hn ih =>
    intro p h
    cases ha : decodePattern a with
    | none => simp [decodePattern, ht, hnot, hn, ha] at h
    | some pat =>
      cases hb : destString b with
      | none => simp [decodePattern, ht, hnot, hn, ha, hb] at h
      | some id =>
        simp [decodePattern, ht, hnot, hn, ha, hb] at h
        subst p
        have ea := ih pat ha
        have eb := (destString_some b id).1.mp hb
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [patsexp, listsexp, ea, eb, hn, ht]
        constructor <;> rfl
  | case11 name a b terminator ht hnot1 hnot2 hn ih =>
    intro p h
    cases ha : decodePattern a with
    | none => simp [decodePattern, ht, hnot1, hnot2, hn, ha] at h
    | some pat =>
      cases hb : decodeType b with
      | none => simp [decodePattern, ht, hnot1, hnot2, hn, ha, hb] at h
      | some ty =>
        simp [decodePattern, ht, hnot1, hnot2, hn, ha, hb] at h
        subst p
        have ea := ih pat ha
        have eb := (decodeType_some b ty).1.mp hb
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [patsexp, listsexp, ea, eb, hn, ht]
        constructor <;> rfl
  | case12 name a b terminator ht hnot1 hnot2 hn =>
    intro p h
    simp [decodePattern, ht, hnot1, hnot2, hn] at h
  | case13 x h1 h2 h3 h4 =>
    intro p h
    rw [decodePattern.eq_def] at h
    split at h <;> simp_all
  | case14 head tail ihh iht ps h =>
    cases hh : decodePattern head with
    | none => simp [decodePatternList, hh] at h
    | some p =>
      cases ht : decodePatternList tail with
      | none => simp [decodePatternList, hh, ht] at h
      | some rest =>
        simp [decodePatternList, hh, ht] at h
        subst ps
        have eh := ihh p hh
        have et := iht rest ht
        simp only [listsexp] at et
        simp [listsexp, eh, et]
  | case15 name hn ps h =>
    simp [decodePatternList, hn] at h
    subst ps
    simp only [beq_iff_eq] at hn
    simp [listsexp, hn]
    rfl
  | case16 name hn ps h =>
    simp [decodePatternList, hn] at h
  | case17 x h1 h2 ps h =>
    rw [decodePatternList.eq_def] at h
    split at h <;> simp_all

/-- Pattern decoding succeeds exactly on the canonical encoding, in both
orientations of option equality. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "patsexp_sexppat"]
theorem decodePattern_some (s : Sexp) (p : Pat) :
    (decodePattern s = some p ↔ patsexp p = s) ∧
    (some p = decodePattern s ↔ patsexp p = s) := by
  have forward : decodePattern s = some p → patsexp p = s := decodePattern_canonical s p
  have backward : patsexp p = s → decodePattern s = some p := by
    intro h
    subst s
    exact decodePattern_patsexp p
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

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

/-- Successful location-point decoding yields the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locnsexp_sexplocpt0"]
theorem decodeLocPoint_canonical (s : Sexp) (z : Locn) (h : decodeLocPoint s = some z) : locnsexp z = s := by
  cases s with
  | sym name =>
    simp only [decodeLocPoint] at h
    split at h
    next unk =>
      simp at h
      subst z
      simp only [beq_iff_eq] at unk
      simp [locnsexp, unk]
      rfl
    next notUnk =>
      split at h
      next eof =>
        simp at h
        subst z
        simp only [beq_iff_eq] at eof
        simp [locnsexp, eof]
        rfl
      next _ => simp at h
  | num _ | str _ => simp [decodeLocPoint, decodeList] at h
  | cons head tail =>
    cases hs : decodeList some (.cons head tail) with
    | none => simp [decodeLocPoint, hs] at h
    | some xs =>
      have shape := (decodeList_some_identity (.cons head tail) xs).mp hs
      cases xs with
      | nil => simp [decodeLocPoint, hs] at h
      | cons a rest =>
        cases rest with
        | nil => simp [decodeLocPoint, hs] at h
        | cons b rest =>
          cases rest with
          | cons c more => simp [decodeLocPoint, hs] at h
          | nil =>
            cases a with
            | num row =>
              cases b with
              | num col =>
                simp [decodeLocPoint, hs] at h
                subst z
                simpa [locnsexp] using shape.symm
              | sym _ | str _ | cons _ _ => simp [decodeLocPoint, hs] at h
            | sym _ | str _ | cons _ _ => simp [decodeLocPoint, hs] at h

/-- Source locations round trip through S-expressions. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplocn_locnsexp"]
theorem decodeLoc_locssexp (loc : Locs) : decodeLoc (locssexp loc) = some loc := by
  cases loc with
  | locs a b =>
    simp (config := { decide := true }) [locssexp, listsexp, decodeLoc, decodeList,
      decodeLocPoint_locnsexp]

/-- Location-point decoding succeeds exactly on the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locnsexp_sexplocpt"]
theorem decodeLocPoint_some (s : Sexp) (z : Locn) :
    (decodeLocPoint s = some z ↔ locnsexp z = s) ∧
    (some z = decodeLocPoint s ↔ locnsexp z = s) := by
  have forward : decodeLocPoint s = some z → locnsexp z = s := decodeLocPoint_canonical s z
  have backward : locnsexp z = s → decodeLocPoint s = some z := by
    intro h
    subst s
    exact decodeLocPoint_locnsexp z
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

/-- Location decoding succeeds exactly on the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locnsexp_sexplocn"]
theorem decodeLoc_some (s : Sexp) (z : Locs) :
    (decodeLoc s = some z ↔ locssexp z = s) ∧
    (some z = decodeLoc s ↔ locssexp z = s) := by
  have forward : decodeLoc s = some z → locssexp z = s := by
    intro h
    unfold decodeLoc at h
    cases hs : decodeList some s with
    | none => simp [hs] at h
    | some xs =>
      have shape := (decodeList_some_identity s xs).mp hs
      cases xs with
      | nil => simp [hs] at h
      | cons a rest =>
        cases rest with
        | nil => simp [hs] at h
        | cons b rest =>
          cases rest with
          | cons c more => simp [hs] at h
          | nil =>
            cases ha : decodeLocPoint a with
            | none => simp [hs, ha] at h
            | some left =>
              cases hb : decodeLocPoint b with
              | none => simp [hs, ha, hb] at h
              | some right =>
                simp [hs, ha, hb] at h
                subst z
                have ea := decodeLocPoint_canonical a left ha
                have eb := decodeLocPoint_canonical b right hb
                simpa [locssexp, ea, eb] using shape.symm
  have backward : locssexp z = s → decodeLoc s = some z := by
    intro h
    subst s
    exact decodeLoc_locssexp z
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

/-- Logical operators round trip through S-expressions. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexplog_logsexp"]
theorem decodeLog_logsexp (op : Lop) : decodeLog (logsexp op) = some op := by
  cases op <;> decide

/-- A symbol name decoded for operator dispatch determines its original bytes.
This describes Flapjack's `symbolName` helper. -/
theorem symbolName_canonical (s : Sexp) (name : String) (h : symbolName s = some name) :
    s = .sym ((ofString name).explode) := by
  cases s with
  | sym bytes =>
    simp [symbolName] at h
    subst name
    simp [ofString_toStringOfBytes]
  | num _ | str _ | cons _ _ => simp [symbolName] at h

/-- A successfully decoded logical operator has its canonical encoding. -/
theorem decodeLog_canonical (s : Sexp) (z : Lop) (h : decodeLog s = some z) : logsexp z = s := by
  cases s with
  | sym name =>
    cases z <;> simp [decodeLog, symbolName] at h <;> split at h <;> simp_all
    all_goals
      rename_i _ heq
      have eq := congrArg (fun text => (ofString text).explode) heq
      simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
      simp only [logsexp, Sexp.sym.injEq]
      convert eq.symm using 1
      rfl
  | num _ | str _ | cons _ _ => simp [decodeLog, symbolName] at h

/-- Logical operator decoding succeeds exactly on the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "logsexp_sexplog"]
theorem decodeLog_some (s : Sexp) (z : Lop) :
    (decodeLog s = some z ↔ logsexp z = s) ∧
    (some z = decodeLog s ↔ logsexp z = s) := by
  have forward : decodeLog s = some z → logsexp z = s := decodeLog_canonical s z
  have backward : logsexp z = s → decodeLog s = some z := by
    intro h
    subst s
    exact decodeLog_logsexp z
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

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

/-- Successful arithmetic-operator decoding yields the canonical symbol. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexparith_arithsexp"]
theorem decodeArith_canonical (s : Sexp) (z : Arith) (h : decodeArith s = some z) : arithsexp z = s := by
  cases s with
  | sym name =>
    cases z <;> simp [decodeArith, symbolName] at h <;> split at h <;> simp_all
    all_goals
      rename_i _ heq
      have eq := congrArg (fun text => (ofString text).explode) heq
      simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
      simp only [arithsexp, Sexp.sym.injEq]
      convert eq.symm using 1
      rfl
  | num _ | str _ | cons _ _ => simp [decodeArith, symbolName] at h

/-- Successful primitive-type decoding yields the canonical symbol. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decode_prim_type_prim_typesexp"]
theorem decodePrimType_canonical (s : Sexp) (z : PrimType) (h : decodePrimType s = some z) : primTypesexp z = s := by
  cases s with
  | sym name =>
    cases z with
    | wordT width =>
      cases width <;> simp [decodePrimType, symbolName] at h <;> split at h <;> simp_all
      all_goals
        rename_i _ heq
        have eq := congrArg (fun text => (ofString text).explode) heq
        simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
        simp only [primTypesexp, Sexp.sym.injEq]
        convert eq.symm using 1
        rfl
    | boolT | intT | charT | strT | float64T =>
      simp [decodePrimType, symbolName] at h
      split at h <;> simp_all
      all_goals
        rename_i _ heq
        have eq := congrArg (fun text => (ofString text).explode) heq
        simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
        simp only [primTypesexp, Sexp.sym.injEq]
        convert eq.symm using 1
        rfl
  | num _ | str _ | cons _ _ => simp [decodePrimType, symbolName] at h

/-- Successful comparison-test decoding yields the canonical symbol. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decode_test_testsexp"]
theorem decodeTest_canonical (s : Sexp) (z : Test) (h : decodeTest s = some z) : testsexp z = s := by
  cases s with
  | sym name =>
    cases z with
    | equal =>
      simp [decodeTest, symbolName] at h
      split at h <;> simp_all
      rename_i _ heq
      have eq := congrArg (fun text => (ofString text).explode) heq
      simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
      simp only [testsexp, Sexp.sym.injEq]
      convert eq.symm using 1
      rfl
    | compare op | altCompare op =>
      cases op <;> simp [decodeTest, symbolName] at h <;> split at h <;> simp_all
      all_goals
        rename_i _ heq
        have eq := congrArg (fun text => (ofString text).explode) heq
        simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
        simp only [testsexp, Sexp.sym.injEq]
        convert eq.symm using 1
        rfl
  | num _ | str _ | cons _ _ => simp [decodeTest, symbolName] at h

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

/-- The nullary operator dispatcher yields the canonical symbol. This is
Flapjack infrastructure for the operator inverse theorem. -/
theorem decodeSimpleOp_canonical (name : String) (op : Op) (h : decodeSimpleOp name = some op) :
    opsexp op = .sym ((ofString name).explode) := by
  unfold decodeSimpleOp at h
  split at h <;> simp_all
  all_goals subst op; rfl

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

/-- Successful operator decoding yields the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "opsexp_sexpop"]
theorem decodeOp_canonical (s : Sexp) (op : Op) (h : decodeOp s = some op) : opsexp op = s := by
  cases s with
  | sym bytes =>
    cases hs : symbolName (.sym bytes) with
    | none => simp [decodeOp, hs] at h
    | some name =>
      simp [decodeOp, hs] at h
      have shape := symbolName_canonical (.sym bytes) name hs
      exact (decodeSimpleOp_canonical name op h).trans shape.symm
  | num _ | str _ => simp [decodeOp] at h
  | cons head tail =>
    cases head with
    | sym name =>
      cases tail with
      | str bytes =>
        simp only [decodeOp] at h
        split at h
        next isFfi =>
          cases hv : destString (.str bytes) with
          | none => simp [hv] at h
          | some value =>
            simp [hv] at h
            subst op
            have encoded := (destString_some (.str bytes) value).1.mp hv
            simp only [beq_iff_eq] at isFfi
            have eq := congrArg (fun text => (ofString text).explode) isFfi
            simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
            simp [opsexp, opSym, encoded, eq]
            rfl
        next notFfi => simp at h
      | sym mode =>
        simp only [decodeOp, symbolName] at h
        dsimp at h
        split at h <;> simp_all
        all_goals split at h <;> simp_all
        all_goals
          first | (have hn := h.1; have ho := h.2; subst op) | subst op
          have en : name = (ofString (toStringOfBytes (.implode name))).explode := by
            simp [ofString_toStringOfBytes]
          have em : mode = (ofString (toStringOfBytes (.implode mode))).explode := by
            simp [ofString_toStringOfBytes]
          rw [en, em]
          clear en em
          simp_all [opsexp, opSym, opMode]
          constructor <;> rfl
      | num n =>
        simp only [decodeOp] at h
        split at h <;> simp_all
        all_goals
          subst op
          rename_i _ heq
          have eq := congrArg (fun text => (ofString text).explode) heq
          simp only [ofString_toStringOfBytes, MlString.explode_implode] at eq
          simp [opsexp, opSym, opShiftName, eq]
          rfl
      | cons left right =>
        simp only [decodeOp] at h
        dsimp at h
        split at h
        next isArith =>
          cases ha : decodeArith left with
          | none => simp [ha] at h
          | some arith =>
            cases hb : decodePrimType right with
            | none => simp [ha, hb] at h
            | some ty =>
              simp [ha, hb] at h
              subst op
              have ea := decodeArith_canonical left arith ha
              have eb := decodePrimType_canonical right ty hb
              simp only [beq_iff_eq] at isArith
              have en := congrArg (fun text => (ofString text).explode) isArith
              simp only [ofString_toStringOfBytes, MlString.explode_implode] at en
              simp [opsexp, opSym, ea, eb, en]
              rfl
        next notArith =>
          split at h
          next isFromTo =>
            cases ha : decodePrimType left with
            | none => simp [ha] at h
            | some fromTy =>
              cases hb : decodePrimType right with
              | none => simp [ha, hb] at h
              | some toTy =>
                simp [ha, hb] at h
                subst op
                have ea := decodePrimType_canonical left fromTy ha
                have eb := decodePrimType_canonical right toTy hb
                simp only [beq_iff_eq] at isFromTo
                have en := congrArg (fun text => (ofString text).explode) isFromTo
                simp only [ofString_toStringOfBytes, MlString.explode_implode] at en
                simp [opsexp, opSym, ea, eb, en]
                rfl
          next notFromTo =>
            split at h
            next isTest =>
              cases ha : decodeTest left with
              | none => simp [ha] at h
              | some test =>
                cases hb : decodePrimType right with
                | none => simp [ha, hb] at h
                | some ty =>
                  simp [ha, hb] at h
                  subst op
                  have ea := decodeTest_canonical left test ha
                  have eb := decodePrimType_canonical right ty hb
                  simp only [beq_iff_eq] at isTest
                  have en := congrArg (fun text => (ofString text).explode) isTest
                  simp only [ofString_toStringOfBytes, MlString.explode_implode] at en
                  simp [opsexp, opSym, ea, eb, en]
                  rfl
            next _ => simp at h
    | num _ | str _ | cons _ _ => simp [decodeOp] at h

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

/-- The expression encoder's byte-string helper is canonical. -/
theorem expsexpString_canonical (s : Sexp) (name : MlString) (h : destString s = some name) :
    expsexpString name = s := by
  simpa [expsexpString] using ((destString_some s name).1.mp h).symm

/-- Optional expression-bound names decode only from their canonical form. -/
theorem decodeStringOption_canonical (s : Sexp) (name : Option MlString)
    (h : decodeOption destString s = some name) : optsexp (name.map expsexpString) = s := by
  rcases (decodeOption_some destString s name).mp h with ⟨rfl, rfl⟩ | ⟨x, s0, rfl, hx, hs⟩
  · rfl
  · have eq := expsexpString_canonical s0 x hx
    subst s0
    rw [hs]
    simp [optsexp, listsexp]
    rfl

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

/-- Successful expression decoding yields the source-shaped encoding. This is
the reverse direction of `expsexp_sexpexp` over the executed decoder. -/
theorem decodeExp_canonical (s : Sexp) : ∀ e, decodeExp s = some e → expsexp e = s := by
  induction s using decodeExp.induct
      (motive2 := fun x => ∀ fs, decodeFunctions x = some fs → listsexp (expsexpFuns fs) = x)
      (motive3 := fun x => ∀ es, decodeExpList x = some es → listsexp (expsexpList es) = x)
      (motive4 := fun x => ∀ ps, decodeClauses x = some ps → listsexp (expsexpClauses ps) = x) with
  | case1 name a term ht =>
    intro e h
    simp [decodeExp, ht] at h
  | case2 name a term ht hn ih =>
    intro e h
    cases h0 : decodeExp a with
    | none => simp [decodeExp, ht, hn, h0] at h
    | some ea =>
      simp [decodeExp, ht, hn, h0] at h
      subst e
      have e0 := ih ea h0
      simp only [beq_iff_eq] at hn
      simp only [bne_iff_ne, not_not] at ht
      simp [expsexp, expsexpNode, listsexp, e0, hn, ht]
      constructor <;> rfl
  | case3 name a term ht hn0 hn =>
    intro e h
    cases h0 : decodeLiteral a with
    | none => simp [decodeExp, ht, hn0, hn, h0] at h
    | some lit =>
      simp [decodeExp, ht, hn0, hn, h0] at h
      subst e
      have e0 := decodeLiteral_canonical a lit h0
      simp only [beq_iff_eq] at hn
      simp only [bne_iff_ne, not_not] at ht
      simp [expsexp, expsexpNode, listsexp, e0, hn, ht]
      constructor <;> rfl
  | case4 name a term ht hn0 hn1 hn =>
    intro e h
    cases h0 : decodeId destString a with
    | none => simp [decodeExp, ht, hn0, hn1, hn, h0] at h
    | some id =>
      simp [decodeExp, ht, hn0, hn1, hn, h0] at h
      subst e
      have e0 := ((decodeId_some id a).mp h0).symm
      simp only [beq_iff_eq] at hn
      simp only [bne_iff_ne, not_not] at ht
      simp [expsexp, expsexpNode, listsexp, e0, hn, ht]
      constructor <;> rfl
  | case5 name a term ht hn0 hn1 hn2 =>
    intro e h
    simp [decodeExp, ht, hn0, hn1, hn2] at h
  | case6 name a b term ht =>
    intro e h
    simp [decodeExp, ht] at h
  | case7 name a b term ht hn iha ihb =>
    intro e h
    cases h0 : decodeExp a with
    | none => simp [decodeExp, ht, hn, h0] at h
    | some ea =>
      cases h1 : decodeClauses b with
      | none => simp [decodeExp, ht, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn, h0, h1] at h
        subst e
        have e0 := iha ea h0
        have e1 := ihb eb h1
        simp only [listsexp] at e1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case8 name a b term ht hn0 hn ihb =>
    intro e h
    cases h0 : decodeOption (decodeId destString) a with
    | none => simp [decodeExp, ht, hn0, hn, h0] at h
    | some ea =>
      cases h1 : decodeExpList b with
      | none => simp [decodeExp, ht, hn0, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn, h0, h1] at h
        subst e
        have e0 := decodeIdOption_canonical a ea h0
        have e1 := ihb eb h1
        simp only [listsexp] at e1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case9 name a b term ht hn0 hn1 hn ihb =>
    intro e h
    cases h0 : destString a with
    | none => simp [decodeExp, ht, hn0, hn1, hn, h0] at h
    | some ea =>
      cases h1 : decodeExp b with
      | none => simp [decodeExp, ht, hn0, hn1, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn1, hn, h0, h1] at h
        subst e
        have e0 := expsexpString_canonical a ea h0
        have e1 := ihb eb h1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case10 name a b term ht hn0 hn1 hn2 hn ihb =>
    intro e h
    cases h0 : decodeOp a with
    | none => simp [decodeExp, ht, hn0, hn1, hn2, hn, h0] at h
    | some ea =>
      cases h1 : decodeExpList b with
      | none => simp [decodeExp, ht, hn0, hn1, hn2, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn1, hn2, hn, h0, h1] at h
        subst e
        have e0 := decodeOp_canonical a ea h0
        have e1 := ihb eb h1
        simp only [listsexp] at e1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case11 name a b term ht hn0 hn1 hn2 hn3 hn iha ihb =>
    intro e h
    cases h0 : decodeExp a with
    | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn, h0] at h
    | some ea =>
      cases h1 : decodeClauses b with
      | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn, h0, h1] at h
        subst e
        have e0 := iha ea h0
        have e1 := ihb eb h1
        simp only [listsexp] at e1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case12 name a b term ht hn0 hn1 hn2 hn3 hn4 hn iha ihb =>
    intro e h
    cases h0 : decodeFunctions a with
    | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn, h0] at h
    | some ea =>
      cases h1 : decodeExp b with
      | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn, h0, h1] at h
        subst e
        have e0 := iha ea h0
        simp only [listsexp] at e0
        have e1 := ihb eb h1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case13 name a b term ht hn0 hn1 hn2 hn3 hn4 hn5 hn iha =>
    intro e h
    cases h0 : decodeExp a with
    | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn, h0] at h
    | some ea =>
      cases h1 : decodeType b with
      | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn, h0, h1] at h
        subst e
        have e0 := iha ea h0
        have e1 := (decodeType_some b eb).1.mp h1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case14 name a b term ht hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn iha =>
    intro e h
    cases h0 : decodeExp a with
    | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn, h0] at h
    | some ea =>
      cases h1 : decodeLoc b with
      | none => simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn, h0, h1] at h
      | some eb =>
        simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn, h0, h1] at h
        subst e
        have e0 := iha ea h0
        have e1 := (decodeLoc_some b eb).1.mp h1
        simp only [beq_iff_eq] at hn
        simp only [bne_iff_ne, not_not] at ht
        simp [expsexp, expsexpNode, listsexp, e0, e1, hn, ht]
        constructor <;> rfl
  | case15 name a b term ht hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7 =>
    intro e h
    simp [decodeExp, ht, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7] at h
  | case16 name a b c term ht =>
    intro e h
    simp [decodeExp, ht] at h
  | case17 name a b c term ht hn ihb ihc =>
    intro e h
    cases h0 : decodeLog a with
    | none => simp [decodeExp, ht, hn, h0] at h
    | some ea =>
      cases h1 : decodeExp b with
      | none => simp [decodeExp, ht, hn, h0, h1] at h
      | some eb =>
        cases h2 : decodeExp c with
        | none => simp [decodeExp, ht, hn, h0, h1, h2] at h
        | some ec =>
          simp [decodeExp, ht, hn, h0, h1, h2] at h
          subst e
          have e0 := (decodeLog_some a ea).1.mp h0
          have e1 := ihb eb h1
          have e2 := ihc ec h2
          simp only [beq_iff_eq] at hn
          simp only [bne_iff_ne, not_not] at ht
          simp [expsexp, expsexpNode, listsexp, e0, e1, e2, hn, ht]
          constructor <;> rfl
  | case18 name a b c term ht hn0 hn iha ihb ihc =>
    intro e h
    cases h0 : decodeExp a with
    | none => simp [decodeExp, ht, hn0, hn, h0] at h
    | some ea =>
      cases h1 : decodeExp b with
      | none => simp [decodeExp, ht, hn0, hn, h0, h1] at h
      | some eb =>
        cases h2 : decodeExp c with
        | none => simp [decodeExp, ht, hn0, hn, h0, h1, h2] at h
        | some ec =>
          simp [decodeExp, ht, hn0, hn, h0, h1, h2] at h
          subst e
          have e0 := iha ea h0
          have e1 := ihb eb h1
          have e2 := ihc ec h2
          simp only [beq_iff_eq] at hn
          simp only [bne_iff_ne, not_not] at ht
          simp [expsexp, expsexpNode, listsexp, e0, e1, e2, hn, ht]
          constructor <;> rfl
  | case19 name a b c term ht hn0 hn1 hn ihb ihc =>
    intro e h
    cases h0 : decodeOption destString a with
    | none => simp [decodeExp, ht, hn0, hn1, hn, h0] at h
    | some ea =>
      cases h1 : decodeExp b with
      | none => simp [decodeExp, ht, hn0, hn1, hn, h0, h1] at h
      | some eb =>
        cases h2 : decodeExp c with
        | none => simp [decodeExp, ht, hn0, hn1, hn, h0, h1, h2] at h
        | some ec =>
          simp [decodeExp, ht, hn0, hn1, hn, h0, h1, h2] at h
          subst e
          have e0 := decodeStringOption_canonical a ea h0
          have e1 := ihb eb h1
          have e2 := ihc ec h2
          simp only [beq_iff_eq] at hn
          simp only [bne_iff_ne, not_not] at ht
          simp [expsexp, expsexpNode, listsexp, e0, e1, e2, hn, ht]
          constructor <;> rfl
  | case20 name a b c term ht hn0 hn1 hn2 =>
    intro e h
    simp [decodeExp, ht, hn0, hn1, hn2] at h
  | case21 x h1 h2 h3 =>
    intro e h
    rw [decodeExp.eq_def] at h
    split at h <;> simp_all
  | case22 name arg body tail ihBody ihTail fs h =>
    cases hn : destString name with
    | none => simp [decodeFunctions, hn] at h
    | some n =>
      cases ha : destString arg with
      | none => simp [decodeFunctions, hn, ha] at h
      | some a =>
        cases hb : decodeExp body with
        | none => simp [decodeFunctions, hn, ha, hb] at h
        | some b =>
          cases ht : decodeFunctions tail with
          | none => simp [decodeFunctions, hn, ha, hb, ht] at h
          | some rest =>
            simp [decodeFunctions, hn, ha, hb, ht] at h
            subst fs
            have en := expsexpString_canonical name n hn
            have ea := expsexpString_canonical arg a ha
            have eb := ihBody b hb
            have et := ihTail rest ht
            simp only [listsexp] at et
            simp [expsexpFuns, listsexp, en, ea, eb, et]
  | case23 name hn fs h =>
    simp [decodeFunctions, hn] at h
    subst fs
    simp only [beq_iff_eq] at hn
    simp [expsexpFuns, listsexp, hn]
    rfl
  | case24 name hn fs h => simp [decodeFunctions, hn] at h
  | case25 x h1 h2 fs h =>
    rw [decodeFunctions.eq_def] at h
    split at h <;> simp_all
    exfalso
    apply h1 <;> rfl
  | case26 head tail ihHead ihTail es h =>
    cases hh : decodeExp head with
    | none => simp [decodeExpList, hh] at h
    | some e =>
      cases ht : decodeExpList tail with
      | none => simp [decodeExpList, hh, ht] at h
      | some rest =>
        simp [decodeExpList, hh, ht] at h
        subst es
        have eh := ihHead e hh
        have et := ihTail rest ht
        simp only [listsexp] at et
        simp [expsexpList, listsexp, eh, et]
  | case27 name hn es h =>
    simp [decodeExpList, hn] at h
    subst es
    simp only [beq_iff_eq] at hn
    simp [expsexpList, listsexp, hn]
    rfl
  | case28 name hn es h => simp [decodeExpList, hn] at h
  | case29 x h1 h2 es h =>
    rw [decodeExpList.eq_def] at h
    split at h <;> simp_all
  | case30 pat body tail ihBody ihTail ps h =>
    cases hp : decodePattern pat with
    | none => simp [decodeClauses, hp] at h
    | some p =>
      cases hb : decodeExp body with
      | none => simp [decodeClauses, hp, hb] at h
      | some b =>
        cases ht : decodeClauses tail with
        | none => simp [decodeClauses, hp, hb, ht] at h
        | some rest =>
          simp [decodeClauses, hp, hb, ht] at h
          subst ps
          have ep := decodePattern_canonical pat p hp
          have eb := ihBody b hb
          have et := ihTail rest ht
          simp only [listsexp] at et
          simp [expsexpClauses, listsexp, ep, eb, et]
  | case31 name hn ps h =>
    simp [decodeClauses, hn] at h
    subst ps
    simp only [beq_iff_eq] at hn
    simp [expsexpClauses, listsexp, hn]
    rfl
  | case32 name hn ps h => simp [decodeClauses, hn] at h
  | case33 x h1 h2 ps h =>
    rw [decodeClauses.eq_def] at h
    split at h <;> simp_all

/-- Expression decoding succeeds exactly on the canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "expsexp_sexpexp"]
theorem decodeExp_some (s : Sexp) (e : Exp) :
    (decodeExp s = some e ↔ expsexp e = s) ∧
    (some e = decodeExp s ↔ expsexp e = s) := by
  have forward : decodeExp s = some e → expsexp e = s := decodeExp_canonical s e
  have backward : expsexp e = s → decodeExp s = some e := by
    intro h
    subst s
    exact decodeExp_expsexp e
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

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

/-- Successful decoding of datatype definitions implies canonical encoding. -/
theorem decodeTypeDef_canonical (s : Sexp) (td : TypeDef)
    (h : decodeTypeDef s = some td) : typeDefsexp td = s := by
  have strings : ∀ s xs, decodeList destString s = some xs →
      listsexp (xs.map expsexpString) = s :=
    decodeList_canonical destString expsexpString expsexpString_canonical
  have constructors : ∀ s xs, decodeList (decodePair destString decodeTypeList) s = some xs →
      listsexp (xs.map (fun (name, ts) => .cons (expsexpString name)
        (listsexp (ts.map typesexp)))) = s := by
    apply decodeList_canonical
    intro s p hp
    obtain ⟨x, y, a, b, ha, hb, rfl, rfl⟩ :=
      (decodePair_some destString decodeTypeList s p).mp hp
    simp [expsexpString_canonical x a ha, decodeTypeList_canonical y b hb]
  unfold decodeTypeDef at h
  unfold typeDefsexp
  apply decodeList_canonical _ _ ?_ s td h
  intro s p hp
  obtain ⟨x, y, a, b, ha, hb, rfl, rfl⟩ :=
    (decodePair_some (decodeList destString)
      (decodePair destString (decodeList (decodePair destString decodeTypeList))) s p).mp hp
  obtain ⟨u, v, c, d, hc, hd, rfl, rfl⟩ :=
    (decodePair_some destString (decodeList (decodePair destString decodeTypeList)) y b).mp hb
  simp [strings x a ha, expsexpString_canonical u c hc, constructors v d hd]

/-- A datatype definition decodes exactly when it is its canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "type_defsexp_sexptype_def"]
theorem decodeTypeDef_some (s : Sexp) (td : TypeDef) :
    (decodeTypeDef s = some td ↔ typeDefsexp td = s) ∧
    (some td = decodeTypeDef s ↔ typeDefsexp td = s) := by
  have forward := decodeTypeDef_canonical s td
  have backward : typeDefsexp td = s → decodeTypeDef s = some td := by
    intro h
    rw [← h]
    exact decodeTypeDef_typeDefsexp td
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "type_defsexp_11"]
theorem typeDefsexp_injective (a b : TypeDef) : typeDefsexp a = typeDefsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeTypeDef h
    simpa [decodeTypeDef_typeDefsexp] using decoded
  · rintro rfl
    rfl

/-- Function-list decoding preserves the canonical expression encoding. -/
theorem decodeFunctions_canonical (s : Sexp) (fs : List (MlString × MlString × Exp))
    (h : decodeFunctions s = some fs) : listsexp (expsexpFuns fs) = s := by
  induction s generalizing fs with
  | sym name =>
    simp only [decodeFunctions] at h
    split at h
    next hn =>
      simp at h
      subst fs
      simp only [beq_iff_eq] at hn
      simp [expsexpFuns, listsexp, hn]
      rfl
    next => contradiction
  | num _ | str _ => simp [decodeFunctions] at h
  | cons head tail _ ih =>
    cases head with
    | sym _ | num _ | str _ => simp [decodeFunctions] at h
    | cons name inner =>
      cases inner with
      | sym _ | num _ | str _ => simp [decodeFunctions] at h
      | cons arg body =>
        cases hn : destString name with
        | none => simp [decodeFunctions, hn] at h
        | some n =>
          cases ha : destString arg with
          | none => simp [decodeFunctions, hn, ha] at h
          | some a =>
            cases hb : decodeExp body with
            | none => simp [decodeFunctions, hn, ha, hb] at h
            | some b =>
              cases ht : decodeFunctions tail with
              | none => simp [decodeFunctions, hn, ha, hb, ht] at h
              | some rest =>
                simp [decodeFunctions, hn, ha, hb, ht] at h
                subst fs
                have en := expsexpString_canonical name n hn
                have ea := expsexpString_canonical arg a ha
                have eb := decodeExp_canonical body b hb
                have et := ih rest ht
                simp only [listsexp] at et
                simp [expsexpFuns, listsexp, en, ea, eb, et]

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

/-- Successful declaration decoding accepts only canonical encodings. -/
theorem decodeDec_canonical (s : Sexp) : ∀ d, decodeDec s = some d → decsexp d = s := by
  induction s using decodeDec.induct
      (motive2 := fun x => ∀ ds, decodeDecList x = some ds → listsexp (decsexpList ds) = x) with
  | case1 name a term hn =>
    intro d h
    cases h0 : destString a with
    | none => simp [decodeDec, hn, h0] at h
    | some v0 =>
      simp [decodeDec, hn, h0] at h
      subst d
      have e0 := expsexpString_canonical a v0 h0
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      try simp only [listsexp] at e0
      simp [decsexp, expsexpNode, listsexp, e0, hn]
      constructor <;> rfl
  | case2 name a term hn =>
    intro d h
    simp [decodeDec, hn] at h
  | case3 name a b term ht =>
    intro d h
    simp [decodeDec, ht] at h
  | case4 name a b term ht hn =>
    intro d h
    cases h0 : decodeLoc a with
    | none => simp [decodeDec, ht, hn, h0] at h
    | some v0 =>
      cases h1 : decodeFunctions b with
      | none => simp [decodeDec, ht, hn, h0, h1] at h
      | some v1 =>
        simp [decodeDec, ht, hn, h0, h1] at h
        subst d
        have e0 := (decodeLoc_some a v0).1.mp h0
        have e1 := decodeFunctions_canonical b v1 h1
        simp only [bne_iff_ne, not_not] at ht
        simp only [beq_iff_eq] at hn
        try simp only [listsexp] at e0 e1
        simp [decsexp, expsexpNode, listsexp, e0, e1, ht, hn]
        constructor <;> rfl
  | case5 name a b term ht hn0 hn =>
    intro d h
    cases h0 : decodeLoc a with
    | none => simp [decodeDec, ht, hn0, hn, h0] at h
    | some v0 =>
      cases h1 : decodeTypeDef b with
      | none => simp [decodeDec, ht, hn0, hn, h0, h1] at h
      | some v1 =>
        simp [decodeDec, ht, hn0, hn, h0, h1] at h
        subst d
        have e0 := (decodeLoc_some a v0).1.mp h0
        have e1 := decodeTypeDef_canonical b v1 h1
        simp only [bne_iff_ne, not_not] at ht
        simp only [beq_iff_eq] at hn
        try simp only [listsexp] at e0 e1
        simp [decsexp, expsexpNode, listsexp, e0, e1, ht, hn]
        constructor <;> rfl
  | case6 name a b term ht hn0 hn1 hn ihb =>
    intro d h
    cases h0 : destString a with
    | none => simp [decodeDec, ht, hn0, hn1, hn, h0] at h
    | some v0 =>
      cases h1 : decodeDecList b with
      | none => simp [decodeDec, ht, hn0, hn1, hn, h0, h1] at h
      | some v1 =>
        simp [decodeDec, ht, hn0, hn1, hn, h0, h1] at h
        subst d
        have e0 := expsexpString_canonical a v0 h0
        have e1 := ihb v1 h1
        simp only [bne_iff_ne, not_not] at ht
        simp only [beq_iff_eq] at hn
        try simp only [listsexp] at e0 e1
        simp [decsexp, expsexpNode, listsexp, e0, e1, ht, hn]
        constructor <;> rfl
  | case7 name a b term ht hn0 hn1 hn2 hn iha ihb =>
    intro d h
    cases h0 : decodeDecList a with
    | none => simp [decodeDec, ht, hn0, hn1, hn2, hn, h0] at h
    | some v0 =>
      cases h1 : decodeDecList b with
      | none => simp [decodeDec, ht, hn0, hn1, hn2, hn, h0, h1] at h
      | some v1 =>
        simp [decodeDec, ht, hn0, hn1, hn2, hn, h0, h1] at h
        subst d
        have e0 := iha v0 h0
        have e1 := ihb v1 h1
        simp only [bne_iff_ne, not_not] at ht
        simp only [beq_iff_eq] at hn
        try simp only [listsexp] at e0 e1
        simp [decsexp, expsexpNode, listsexp, e0, e1, ht, hn]
        constructor <;> rfl
  | case8 name a b term ht hn0 hn1 hn2 hn3 =>
    intro d h
    simp [decodeDec, ht, hn0, hn1, hn2, hn3] at h
  | case9 name a b c term ht =>
    intro d h
    simp [decodeDec, ht] at h
  | case10 name a b c term ht hn =>
    intro d h
    cases h0 : decodeLoc a with
    | none => simp [decodeDec, ht, hn, h0] at h
    | some v0 =>
      cases h1 : decodePattern b with
      | none => simp [decodeDec, ht, hn, h0, h1] at h
      | some v1 =>
        cases h2 : decodeExp c with
        | none => simp [decodeDec, ht, hn, h0, h1, h2] at h
        | some v2 =>
          simp [decodeDec, ht, hn, h0, h1, h2] at h
          subst d
          have e0 := (decodeLoc_some a v0).1.mp h0
          have e1 := decodePattern_canonical b v1 h1
          have e2 := decodeExp_canonical c v2 h2
          simp only [bne_iff_ne, not_not] at ht
          simp only [beq_iff_eq] at hn
          try simp only [listsexp] at e0 e1 e2
          simp [decsexp, expsexpNode, listsexp, e0, e1, e2, ht, hn]
          constructor <;> rfl
  | case11 name a b c term ht hn0 hn =>
    intro d h
    cases h0 : decodeLoc a with
    | none => simp [decodeDec, ht, hn0, hn, h0] at h
    | some v0 =>
      cases h1 : destString b with
      | none => simp [decodeDec, ht, hn0, hn, h0, h1] at h
      | some v1 =>
        cases h2 : decodeTypeList c with
        | none => simp [decodeDec, ht, hn0, hn, h0, h1, h2] at h
        | some v2 =>
          simp [decodeDec, ht, hn0, hn, h0, h1, h2] at h
          subst d
          have e0 := (decodeLoc_some a v0).1.mp h0
          have e1 := expsexpString_canonical b v1 h1
          have e2 := decodeTypeList_canonical c v2 h2
          simp only [bne_iff_ne, not_not] at ht
          simp only [beq_iff_eq] at hn
          try simp only [listsexp] at e0 e1 e2
          simp [decsexp, expsexpNode, listsexp, e0, e1, e2, ht, hn]
          constructor <;> rfl
  | case12 name a b c term ht hn0 hn1 =>
    intro d h
    simp [decodeDec, ht, hn0, hn1] at h
  | case13 name a b c d0 term ht =>
    intro d h
    simp [decodeDec, ht] at h
  | case14 name a b c d0 term ht hn =>
    intro d h
    cases h0 : decodeLoc a with
    | none => simp [decodeDec, ht, hn, h0] at h
    | some v0 =>
      cases h1 : decodeList destString b with
      | none => simp [decodeDec, ht, hn, h0, h1] at h
      | some v1 =>
        cases h2 : destString c with
        | none => simp [decodeDec, ht, hn, h0, h1, h2] at h
        | some v2 =>
          cases h3 : decodeType d0 with
          | none => simp [decodeDec, ht, hn, h0, h1, h2, h3] at h
          | some v3 =>
            simp [decodeDec, ht, hn, h0, h1, h2, h3] at h
            subst d
            have e0 := (decodeLoc_some a v0).1.mp h0
            have e1 := decodeList_canonical destString expsexpString expsexpString_canonical b v1 h1
            have e2 := expsexpString_canonical c v2 h2
            have e3 := decodeType_canonical d0 v3 h3
            simp only [bne_iff_ne, not_not] at ht
            simp only [beq_iff_eq] at hn
            try simp only [listsexp] at e0 e1 e2 e3
            simp [decsexp, expsexpNode, listsexp, e0, e1, e2, e3, ht, hn]
            constructor <;> rfl
  | case15 name a b c d0 term ht hn =>
    intro d h
    simp [decodeDec, ht, hn] at h
  | case16 x h1 h2 h3 h4 =>
    intro d h
    rw [decodeDec.eq_def] at h
    split at h <;> simp_all
  | case17 head tail ihHead ihTail ds h =>
    cases hh : decodeDec head with
    | none => simp [decodeDecList, hh] at h
    | some d =>
      cases ht : decodeDecList tail with
      | none => simp [decodeDecList, hh, ht] at h
      | some rest =>
        simp [decodeDecList, hh, ht] at h
        subst ds
        have eh := ihHead d hh
        have et := ihTail rest ht
        simp only [listsexp] at et
        simp [decsexpList, listsexp, eh, et]
  | case18 name hn ds h =>
    simp [decodeDecList, hn] at h
    subst ds
    simp only [beq_iff_eq] at hn
    simp [decsexpList, listsexp, hn]
    rfl
  | case19 name hn ds h => simp [decodeDecList, hn] at h
  | case20 x h1 h2 ds h =>
    rw [decodeDecList.eq_def] at h
    split at h <;> simp_all

/-- A declaration decodes exactly when it is its canonical encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decsexp_sexpdec"]
theorem decodeDec_some (s : Sexp) (d : Dec) :
    (decodeDec s = some d ↔ decsexp d = s) ∧
    (some d = decodeDec s ↔ decsexp d = s) := by
  have forward := decodeDec_canonical s d
  have backward : decsexp d = s → decodeDec s = some d := by
    intro h
    rw [← h]
    exact decodeDec_decsexp d
  exact ⟨⟨forward, backward⟩, ⟨fun h => forward h.symm, fun h => (backward h).symm⟩⟩

@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decsexp_11"]
theorem decsexp_injective (a b : Dec) : decsexp a = decsexp b ↔ a = b := by
  constructor
  · intro h
    have decoded := congrArg decodeDec h
    simpa [decodeDec_decsexp] using decoded
  · rintro rfl
    rfl

end Flapjack.CakeParser.FromSexp
