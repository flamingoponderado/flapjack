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

end Flapjack.CakeParser.FromSexp
