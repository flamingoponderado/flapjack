module

public import Flapjack.CakeParser.FromSexp.SexpLemmas

@[expose] public section

/-!
# Simple-S-expression validity

Untagged Lean renderings of HOL's `simpleSexp$valid_sexp` family and the
`fromSexp` validity theorems for the S-expression encoders in
`cakeml/compiler/parsing/fromSexpScript.sml:2140-2320`.

`validSexp` follows `valid_sexp_def` clause for clause: symbols need a valid
symbol, cons cells are valid when both components are, strings need every byte
printable, and numbers are valid.  The character predicates follow
`HOL/src/string/stringScript.sml` (`isDigit`, `isSpace`, `isGraph`, `isPrint`).
-/

namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString

private def ascii (s : String) : List HolChar := (ofString s).explode

/-- HOL `string$isDigit`: the byte is an ASCII decimal digit. -/
def isDigitChar (c : HolChar) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- HOL `string$isSpace`: the byte is a space or a control whitespace. -/
def isSpaceChar (c : HolChar) : Bool := c.toNat == 32 || (9 ≤ c.toNat && c.toNat ≤ 13)

/-- HOL `string$isGraph`: printable and not whitespace. -/
def isGraphChar (c : HolChar) : Bool := isPrint c && !isSpaceChar c

/-- HOL `simpleSexp$valid_first_symchar`. -/
def validFirstSymchar (c : HolChar) : Bool :=
  isGraphChar c && c.toNat != 39 && c.toNat != 40 && c.toNat != 41 &&
    c.toNat != 46 && c.toNat != 34 && !isDigitChar c

/-- HOL `simpleSexp$valid_symchar`. -/
def validSymchar (c : HolChar) : Bool :=
  isGraphChar c && c.toNat != 39 && c.toNat != 40 && c.toNat != 41

/-- HOL `simpleSexp$valid_symbol`: nonempty, valid first byte, valid rest. -/
def validSymbol : List HolChar → Bool
  | [] => false
  | c :: cs => validFirstSymchar c && cs.all validSymchar

/-- HOL `simpleSexp$valid_sexp`. -/
def validSexp : Sexp → Bool
  | .sym s => validSymbol s
  | .cons a b => validSexp a && validSexp b
  | .str s => s.all isPrint
  | .num _ => true

/-- Hex digits are printable bytes. -/
private theorem isPrint_hexDigit (n : Nat) (hn : n < 16) : isPrint (hexDigit n) = true := by
  interval_cases n
  all_goals rfl

/-- Original `EVERY_isPrint_encode_control`: encoding yields printable bytes. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "EVERY_isPrint_encode_control"]
theorem encodeControl_all_isPrint (ls : List HolChar) : (encodeControl ls).all isPrint = true := by
  induction ls with
  | nil => rfl
  | cons c cs ih =>
    have hsingle : (encodeControl [c]).all isPrint = true := by
      unfold encodeControl
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      split
      · rename_i h92
        have hn : c.toNat = 92 := by simpa using h92
        simp [isPrint, hn]
      · split
        · rename_i hprint
          simp [isPrint, hprint]
        · rename_i h92 hprint
          have hdiv : c.toNat / 16 < 16 := by
            have := c.isLt
            omega
          have hmod : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
          simp only [List.all_cons, List.all_nil, Bool.and_true]
          rw [isPrint_hexDigit _ hdiv, isPrint_hexDigit _ hmod]
          simp [isPrint]
    rw [show encodeControl (c :: cs) = encodeControl [c] ++ encodeControl cs from by
      simp [encodeControl]]
    rw [List.all_append, hsingle, ih]
    rfl

/-- Original `SEXSTR_valid`: encoded strings are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "SEXSTR_valid"]
theorem validSexp_sexstr (s : List HolChar) : validSexp (sexstr s) = true :=
  encodeControl_all_isPrint s

/-- Original `listsexp_valid`: lists of valid sexps are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "listsexp_valid"]
theorem validSexp_listsexp (ls : List Sexp) (h : ∀ x, x ∈ ls → validSexp x = true) :
    validSexp (listsexp ls) = true := by
  induction ls with
  | nil => decide
  | cons x xs ih =>
    have hx : validSexp x = true := h x (by simp)
    have hxs : validSexp (listsexp xs) = true := ih (fun y hy => h y (by simp [hy]))
    simp only [listsexp, List.foldr_cons]
    change validSexp (Sexp.cons x (listsexp xs)) = true
    simp [validSexp, hx, hxs]

/-- Original `idsexp_valid`: encoded identifiers are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "idsexp_valid"]
theorem validSexp_idsexp (i : Flapjack.NamespaceHOL.Ident MlString MlString) :
    validSexp (idsexp i) = true := by
  induction i with
  | short name =>
    simp only [idsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact validSexp_sexstr _
  | long moduleName rest ih =>
    simp only [idsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · decide
    · exact validSexp_sexstr _
    · exact ih

/-- Original `litsexp_valid`: encoded literals are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "litsexp_valid"]
theorem validSexp_litsexp (l : Flapjack.AstHOL.Lit) : validSexp (litsexp l) = true := by
  cases l with
  | intLit i =>
    cases i with
    | ofNat n => rfl
    | negSucc n =>
      simp only [litsexp]
      refine validSexp_listsexp _ ?_
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · decide
      · rfl
  | char c =>
    simp only [litsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact validSexp_sexstr _
  | strLit s => exact validSexp_sexstr _
  | word8 w =>
    simp only [litsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · rfl
  | word64 w =>
    simp only [litsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · rfl
  | float64 w =>
    simp only [litsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · rfl

/-- Original `optsexp_valid`: encoded options are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "optsexp_valid"]
theorem validSexp_optsexp (x : Option Sexp) (h : ∀ y, x = some y → validSexp y = true) :
    validSexp (optsexp x) = true := by
  cases x with
  | none => decide
  | some y =>
    have hy : validSexp y = true := h y rfl
    simp only [optsexp]
    refine validSexp_listsexp _ ?_
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · decide
    · exact hy

/-- Original `locnsexp_valid`: encoded location points are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locnsexp_valid"]
theorem validSexp_locnsexp (p : Flapjack.Misc.Location.Locn) : validSexp (locnsexp p) = true := by
  cases p with
  | unknownPt => decide
  | eofPt => decide
  | posn row col =>
    simp only [locnsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · rfl

/-- Original `locssexp_valid`: encoded locations are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locssexp_valid"]
theorem validSexp_locssexp (l : Flapjack.Misc.Location.Locs) : validSexp (locssexp l) = true := by
  obtain ⟨a, b⟩ := l
  simp only [locssexp]
  refine validSexp_listsexp _ ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact validSexp_locnsexp _
  · exact validSexp_locnsexp _

/-- Original `valid_sexp_prim_typesexp`: encoded primitive types are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "valid_sexp_prim_typesexp"]
theorem validSexp_primTypesexp (t : Flapjack.AstHOL.PrimType) :
    validSexp (primTypesexp t) = true := by
  cases t with
  | boolT => decide
  | intT => decide
  | charT => decide
  | strT => decide
  | wordT w =>
    cases w with
    | w8 => decide
    | w64 => decide
  | float64T => decide

/-- Original `typesexp_valid`: encoded type syntax is valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "typesexp_valid"]
theorem validSexp_typesexp (t : Flapjack.AstHOL.AstT) : validSexp (typesexp t) = true := by
  refine typesexp.induct (fun t => validSexp (typesexp t) = true)
    (fun ts => ∀ x, x ∈ typesexpList ts → validSexp x = true) ?_ ?_ ?_ ?_ ?_ ?_ t
  · intro name
    simp only [typesexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact validSexp_sexstr _
  · intro left right ihl ihr
    simp only [typesexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · decide
    · exact ihl
    · exact ihr
  · intro types ih
    simp only [typesexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ih y hy
  · intro types id ih
    simp only [typesexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · decide
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ih y hy
    · exact validSexp_idsexp _
  · intro x hx
    simp only [typesexpList] at hx
    simp at hx
  · intro t ts iht ihts x hx
    simp only [typesexpList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact iht
    · exact ihts x hx

/-- Original `patsexp_valid`: encoded patterns are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "patsexp_valid"]
theorem validSexp_patsexp (p : Flapjack.AstHOL.Pat) : validSexp (patsexp p) = true := by
  refine patsexp.induct (fun p => validSexp (patsexp p) = true)
    (fun ps => ∀ x, x ∈ patsexpList ps → validSexp x = true) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
  · simp only [patsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    decide
  · intro name
    simp only [patsexp]
    exact validSexp_sexstr _
  · intro lit
    simp only [patsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact validSexp_litsexp _
  · intro con pats ih
    simp only [patsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · decide
    · refine validSexp_optsexp _ ?_
      intro y hy
      cases con with
      | none => simp [Option.map] at hy
      | some id =>
        simp only [Option.map_some, Option.some.injEq] at hy
        rw [← hy]
        exact validSexp_idsexp _
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ih y hy
  · intro pat ih
    simp only [patsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact ih
  · intro pat name ih
    simp only [patsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · decide
    · exact ih
    · exact validSexp_sexstr _
  · intro pat type ih
    simp only [patsexp]
    refine validSexp_listsexp _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · decide
    · exact ih
    · exact validSexp_typesexp _
  · intro x hx
    simp only [patsexpList] at hx
    simp at hx
  · intro p ps ihp ihps x hx
    simp only [patsexpList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ihp
    · exact ihps x hx

/-- A mapped list is valid when every encoded element is. -/
private theorem validSexp_listsexp_map {α : Type} (f : α → Sexp) (xs : List α)
    (h : ∀ x, x ∈ xs → validSexp (f x) = true) :
    validSexp (listsexp (xs.map f)) = true := by
  refine validSexp_listsexp _ ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact h x hx

/-- Encoded identifier names are valid strings. -/
private theorem validSexp_expsexpString (s : MlString) : validSexp (expsexpString s) = true :=
  validSexp_sexstr _

/-- Original `type_defsexp_valid`: encoded datatype definitions are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "type_defsexp_valid"]
theorem validSexp_typeDefsexp (td : Flapjack.AstHOL.TypeDef) :
    validSexp (typeDefsexp td) = true := by
  unfold typeDefsexp
  refine validSexp_listsexp_map _ td ?_
  intro entry hentry
  obtain ⟨vs, name, cs⟩ := entry
  simp only [validSexp, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · exact validSexp_listsexp_map _ vs (fun v _ => validSexp_expsexpString _)
  · refine ⟨validSexp_expsexpString _, ?_⟩
    refine validSexp_listsexp_map _ cs ?_
    intro ct hct
    obtain ⟨c, ts⟩ := ct
    simp only [validSexp, Bool.and_eq_true]
    exact ⟨validSexp_expsexpString _, validSexp_listsexp_map _ ts (fun t _ => validSexp_typesexp t)⟩

/-- Original `opsexp_valid`: encoded primitive operators are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "opsexp_valid"]
theorem validSexp_opsexp (op : Flapjack.AstHOL.Op) : validSexp (opsexp op) = true := by
  cases op
  all_goals try decide
  case arith a p =>
    simp only [opsexp, validSexp, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩
    · decide
    · cases a
      all_goals decide
    · exact validSexp_primTypesexp p
  case fromTo a b =>
    simp only [opsexp, validSexp, Bool.and_eq_true]
    exact ⟨by decide, validSexp_primTypesexp a, validSexp_primTypesexp b⟩
  case shift w sh n =>
    simp only [opsexp, validSexp, Bool.and_eq_true]
    refine ⟨?_, trivial⟩
    cases w
    all_goals cases sh
    all_goals decide
  case test t p =>
    simp only [opsexp, validSexp, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩
    · decide
    · cases t with
      | equal => decide
      | compare o =>
        cases o
        all_goals decide
      | altCompare o =>
        cases o
        all_goals decide
    · exact validSexp_primTypesexp p
  case thunkOp o =>
    cases o with
    | allocThunk m =>
      cases m
      all_goals decide
    | updateThunk m =>
      cases m
      all_goals decide
    | forceThunk => decide
  case ffi s =>
    simp only [opsexp, validSexp, Bool.and_eq_true]
    exact ⟨by decide, validSexp_sexstr _⟩

/-- A constructor node is valid when its name and all arguments are. -/
private theorem validSexp_node (name : String) (xs : List Sexp)
    (hname : validSexp (.sym ((ofString name).explode)) = true)
    (h : ∀ x, x ∈ xs → validSexp x = true) :
    validSexp (expsexpNode name xs) = true := by
  unfold expsexpNode
  refine validSexp_listsexp _ ?_
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · rw [ascii_eq_ofString_explode]
    exact hname
  · exact h y hy

/-- Original `expsexp_valid`: encoded expressions are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "expsexp_valid"]
theorem validSexp_expsexp (e : Flapjack.AstHOL.Exp) : validSexp (expsexp e) = true := by
  refine expsexp.induct (fun e => validSexp (expsexp e) = true)
    (fun fs => ∀ x, x ∈ expsexpFuns fs → validSexp x = true)
    (fun es => ∀ x, x ∈ expsexpList es → validSexp x = true)
    (fun ps => ∀ x, x ∈ expsexpClauses ps → validSexp x = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro e ih
    simp only [expsexp]
    refine validSexp_node "Raise" _ (by decide) ?_
    intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact ih
  · intro e ps ih ihps
    simp only [expsexp]
    refine validSexp_node "Handle" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ih
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ihps y hy
  · intro l
    simp only [expsexp]
    refine validSexp_node "Lit" _ (by decide) ?_
    intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact validSexp_litsexp _
  · intro id es ih
    simp only [expsexp]
    refine validSexp_node "Con" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · refine validSexp_optsexp _ ?_
      intro y hy
      cases id with
      | none => simp [Option.map] at hy
      | some i =>
        simp only [Option.map_some, Option.some.injEq] at hy
        rw [← hy]
        exact validSexp_idsexp _
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ih y hy
  · intro id
    simp only [expsexp]
    refine validSexp_node "Var" _ (by decide) ?_
    intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact validSexp_idsexp _
  · intro n e ih
    simp only [expsexp]
    refine validSexp_node "Fun" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact validSexp_expsexpString _
    · exact ih
  · intro o es ih
    simp only [expsexp]
    refine validSexp_node "App" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact validSexp_opsexp _
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ih y hy
  · intro o a b iha ihb
    simp only [expsexp]
    refine validSexp_node "Log" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · cases o
      all_goals decide
    · exact iha
    · exact ihb
  · intro a b c iha ihb ihc
    simp only [expsexp]
    refine validSexp_node "If" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals first | decide | exact iha | exact ihb | exact ihc
  · intro e ps ih ihps
    simp only [expsexp]
    refine validSexp_node "Mat" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ih
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ihps y hy
  · intro n a b iha ihb
    simp only [expsexp]
    refine validSexp_node "Let" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · refine validSexp_optsexp _ ?_
      intro y hy
      cases n with
      | none => simp [Option.map] at hy
      | some name =>
        simp only [Option.map_some, Option.some.injEq] at hy
        rw [← hy]
        exact validSexp_expsexpString _
    · exact iha
    · exact ihb
  · intro fs e ihfs ihe
    simp only [expsexp]
    refine validSexp_node "Letrec" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · refine validSexp_listsexp _ ?_
      intro y hy
      exact ihfs y hy
    · exact ihe
  · intro e t ih
    simp only [expsexp]
    refine validSexp_node "Tannot" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ih
    · exact validSexp_typesexp _
  · intro e l ih
    simp only [expsexp]
    refine validSexp_node "Lannot" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ih
    · exact validSexp_locssexp _
  · intro x hx
    simp only [expsexpFuns] at hx
    simp at hx
  · intro f x e fs ihe ihfs y hy
    simp only [expsexpFuns, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp only [validSexp, Bool.and_eq_true]
      exact ⟨validSexp_expsexpString _, validSexp_expsexpString _, ihe⟩
    · exact ihfs y hy
  · intro x hx
    simp only [expsexpList] at hx
    simp at hx
  · intro e es ihe ihes x hx
    simp only [expsexpList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ihe
    · exact ihes x hx
  · intro x hx
    simp only [expsexpClauses] at hx
    simp at hx
  · intro p e ps ihe ihps y hy
    simp only [expsexpClauses, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp only [validSexp, Bool.and_eq_true]
      exact ⟨validSexp_patsexp _, ihe⟩
    · exact ihps y hy

/-- Every encoded function binding is a valid node. -/
private theorem validSexp_expsexpFuns
    (fs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × Flapjack.AstHOL.Exp)) :
    ∀ x, x ∈ expsexpFuns fs → validSexp x = true := by
  intro x hx
  induction fs with
  | nil =>
    simp only [expsexpFuns] at hx
    simp at hx
  | cons fh ft ih =>
    obtain ⟨f, x', e⟩ := fh
    simp only [expsexpFuns, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [validSexp, Bool.and_eq_true]
      exact ⟨validSexp_expsexpString _, validSexp_expsexpString _, validSexp_expsexp e⟩
    · exact ih hx

/-- Mapped identifier-name lists are valid. -/
private theorem validSexp_listsexp_map_string (xs : List MlString) :
    validSexp (listsexp (xs.map expsexpString)) = true :=
  validSexp_listsexp_map _ xs (fun v _ => validSexp_expsexpString v)

/-- Mapped type lists are valid. -/
private theorem validSexp_listsexp_map_types (ts : List Flapjack.AstHOL.AstT) :
    validSexp (listsexp (ts.map typesexp)) = true :=
  validSexp_listsexp_map _ ts (fun t _ => validSexp_typesexp t)

/-- A list of encoded declarations is valid. -/
private theorem validSexp_listsexp_decsexpList (ds : List Flapjack.AstHOL.Dec)
    (h : ∀ x, x ∈ decsexpList ds → validSexp x = true) :
    validSexp (listsexp (decsexpList ds)) = true :=
  validSexp_listsexp _ h

/-- Original `decsexp_valid`: encoded declarations are valid. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decsexp_valid"]
theorem validSexp_decsexp (d : Flapjack.AstHOL.Dec) : validSexp (decsexp d) = true := by
  refine decsexp.induct (fun d => validSexp (decsexp d) = true)
    (fun ds => ∀ x, x ∈ decsexpList ds → validSexp x = true) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d
  · intro l p e
    simp only [decsexp]
    refine validSexp_node "Dlet" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact validSexp_locssexp _
    · exact validSexp_patsexp _
    · exact validSexp_expsexp _
  · intro l fs
    simp only [decsexp]
    refine validSexp_node "Dletrec" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact validSexp_locssexp _
    · exact validSexp_listsexp _ (validSexp_expsexpFuns fs)
  · intro l td
    simp only [decsexp]
    refine validSexp_node "Dtype" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact validSexp_locssexp _
    · exact validSexp_typeDefsexp _
  · intro l ns n t
    simp only [decsexp]
    refine validSexp_node "Dtabbrev" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact validSexp_locssexp _
    · exact validSexp_listsexp_map_string ns
    · exact validSexp_expsexpString _
    · exact validSexp_typesexp _
  · intro l n ts
    simp only [decsexp]
    refine validSexp_node "Dexn" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact validSexp_locssexp _
    · exact validSexp_expsexpString _
    · exact validSexp_listsexp_map_types ts
  · intro n ds ih
    simp only [decsexp]
    refine validSexp_node "Dmod" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact validSexp_expsexpString _
    · exact validSexp_listsexp_decsexpList ds ih
  · intro a b iha ihb
    simp only [decsexp]
    refine validSexp_node "Dlocal" _ (by decide) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact validSexp_listsexp_decsexpList a iha
    · exact validSexp_listsexp_decsexpList b ihb
  · intro n
    simp only [decsexp]
    refine validSexp_node "Denv" _ (by decide) ?_
    intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact validSexp_expsexpString _
  · intro x hx
    simp only [decsexpList] at hx
    simp at hx
  · intro d ds ih ihs x hx
    simp only [decsexpList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih
    · exact ihs x hx

end Flapjack.CakeParser.FromSexp
