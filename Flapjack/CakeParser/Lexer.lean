import Flapjack.CakeParser.Tokens
import Flapjack.Misc.Location

/-! CakeML lexer infrastructure, operating on HOL's byte-valued characters. -/
namespace Flapjack.CakeParser.Lexer
open Flapjack.Basis.Pure.MlString
open Flapjack.Misc.Location

/-- Intermediate symbols emitted by the original functional lexer. -/
@[hol "cakeml/semantics/lexer_funScript.sml" "symbol"]
inductive Symbol where
  | stringS : List HolChar → Symbol
  | charS : HolChar → Symbol
  | numberS : Int → Symbol
  | wordS : Nat → Symbol
  | longS : List (List HolChar) → List HolChar → Symbol
  | ffiS : List HolChar → Symbol
  | otherS : List HolChar → Symbol
  | errorS
  deriving DecidableEq, Repr

private def ascii (s : String) : List HolChar := (ofString s).explode
private def isAlpha (c : HolChar) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)
private def isDigit (c : HolChar) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57
private def isHex (c : HolChar) : Bool :=
  isDigit c || (65 ≤ c.toNat && c.toNat ≤ 70) || (97 ≤ c.toNat && c.toNat ≤ 102)
private def isSpace (c : HolChar) : Bool := c.toNat == 32 || (9 ≤ c.toNat && c.toNat ≤ 13)
private def isAlphaNumPrime (c : HolChar) : Bool := isAlpha c || isDigit c || c == 39 || c == 95
private def isSingle (c : HolChar) : Bool := (ascii "()[]{},;").contains c
private def isSymbol (c : HolChar) : Bool := (ascii "`!%&$#+-/:<=>?@\\~^|*").contains c

/-- Advance a source position by a column count, retaining sentinels. -/
@[hol "cakeml/semantics/lexer_funScript.sml" "next_loc_def"]
def nextLoc (n : Nat) : Locn → Locn
  | .posn row col => .posn row (col + n)
  | x => x

/-- Advance to the start of the next source line. -/
@[hol "cakeml/semantics/lexer_funScript.sml" "next_line_def"]
def nextLine : Locn → Locn
  | .posn row _ => .posn (row + 1) 0
  | x => x

private def words : List (String × Token) :=
  [("#", .hashT), ("(", .lparT), (")", .rparT), ("*", .starT), (",", .commaT),
   ("->", .arrowT), ("...", .dotsT), (":", .colonT), (":>", .sealT),
   (";", .semicolonT), ("=", .equalsT), ("=>", .darrowT), ("[", .lbrackT),
   ("]", .rbrackT), ("_", .underbarT), ("{", .lbraceT), ("}", .rbraceT), ("|", .barT),
   ("and", .andT), ("andalso", .andalsoT), ("as", .asT), ("case", .caseT),
   ("datatype", .datatypeT), ("else", .elseT), ("end", .endT), ("eqtype", .eqtypeT),
   ("exception", .exceptionT), ("fn", .fnT), ("fun", .funT), ("handle", .handleT),
   ("if", .ifT), ("in", .inT), ("include", .includeT), ("let", .letT),
   ("local", .localT), ("of", .ofT), ("op", .opT), ("open", .openT),
   ("orelse", .orelseT), ("raise", .raiseT), ("rec", .recT), ("sharing", .sharingT),
   ("sig", .sigT), ("signature", .signatureT), ("struct", .structT), ("structure", .structureT),
   ("then", .thenT), ("type", .typeT), ("val", .valT), ("where", .whereT),
   ("with", .withT), ("withtype", .withtypeT)]

/-- Convert a lexed identifier or punctuation spelling to its CakeML token. -/
@[hol "cakeml/semantics/lexer_funScript.sml" "get_token_def"]
def getToken (s : List HolChar) : Token :=
  match words.find? (fun (word, _) => ascii word == s) with
  | some (_, token) => token
  | none => match s with
      | [] => .lexErrorT
      | c :: _ => if c == 39 then .tyvarT (.implode s)
          else if isAlpha c then .alphaT (.implode s) else .symbolT (.implode s)

/-- Turn a list of module identifiers into the source path carrier. -/
@[hol "cakeml/semantics/lexer_funScript.sml" "to_path_def"]
def toPath : List MlString → Path
  | [] => .end
  | x :: xs => .mod x (toPath xs)

/-- Convert an intermediate symbol to the corresponding token. -/
@[hol "cakeml/semantics/lexer_funScript.sml" "token_of_sym_def"]
def tokenOfSymbol : Symbol → Token
  | .errorS => .lexErrorT
  | .stringS s => .stringT (.implode s)
  | .charS c => .charT c
  | .numberS i => .intT i
  | .wordS n => .wordT n
  | .longS xs s => .longidT (toPath (xs.map .implode)) (.implode s)
  | .ffiS s => .ffiT (.implode s)
  | .otherS s => getToken s

private def readWhile (p : HolChar → Bool) : List HolChar → List HolChar × List HolChar
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (yes, rest) := readWhile p cs
        (c :: yes, rest)
      else ([], c :: cs)

private def number (base : Nat) (digits : List HolChar) : Nat :=
  digits.foldl (fun n c =>
    let v := c.toNat
    let digit := if v ≤ 57 then v - 48 else if v ≤ 70 then v - 55 else v - 87
    n * base + digit) 0

private def readStringFuel : Nat → List HolChar → List HolChar → Locn →
    Option (Symbol × Locn × List HolChar)
  | 0, _, _, _ => none
  | _ + 1, [], _, loc => some (.errorS, loc, [])
  | fuel + 1, c :: cs, acc, loc =>
      if c == 34 then some (.stringS acc, loc, cs)
      else if c == 10 then some (.errorS, nextLine loc, cs)
      else if c != 92 then readStringFuel fuel cs (acc ++ [c]) (nextLoc 1 loc)
      else match cs with
        | [] => some (.errorS, loc, [])
        | x :: rest =>
            let value : Option HolChar := match x.toNat with
              | 92 => some 92 | 34 => some 34 | 97 => some 7 | 98 => some 8
              | 116 => some 9 | 110 => some 10 | 118 => some 11 | 102 => some 12 | 114 => some 13
              | _ => none
            match value with
            | some v => readStringFuel fuel rest (acc ++ [v]) (nextLoc 2 loc)
            | none =>
                if isDigit x then
                  let ds := cs.take 3
                  if ds.length == 3 && ds.all isDigit && number 10 ds < 256 then
                    readStringFuel fuel (cs.drop 3) (acc ++ [BitVec.ofNat 8 (number 10 ds)]) (nextLoc 4 loc)
                  else some (.errorS, loc, cs)
                else some (.errorS, loc, cs)

private def skipCommentFuel : Nat → List HolChar → Nat → Locn → Option (Option (List HolChar × Locn))
  | 0, _, _, _ => none
  | _ + 1, [], _, _ | _ + 1, [_], _, _ => some none
  | fuel + 1, x :: y :: xs, depth, loc =>
      if x == 40 && y == 42 then skipCommentFuel fuel xs (depth + 1) (nextLoc 2 loc)
      else if x == 42 && y == 41 then
        if depth == 0 then some (some (xs, nextLoc 2 loc))
        else skipCommentFuel fuel xs (depth - 1) (nextLoc 2 loc)
      else if x == 10 then skipCommentFuel fuel (y :: xs) depth (nextLine loc)
      else skipCommentFuel fuel (y :: xs) depth (nextLoc 1 loc)

private def readFfiFuel : Nat → List HolChar → List HolChar → Locn → Option (Symbol × Locn × List HolChar)
  | 0, _, _, _ => none
  | _ + 1, [], _, loc => some (.errorS, loc, [])
  | fuel + 1, c :: cs, acc, loc =>
      if c == 41 then some (.ffiS acc, nextLoc 2 loc, cs)
      else if c == 10 then some (.errorS, loc, cs)
      else if isSpace c then readFfiFuel fuel cs acc (nextLoc 1 loc)
      else readFfiFuel fuel cs (acc ++ [c]) (nextLoc 1 loc)

private def readIdentFuel : Nat → List HolChar → Locn → List (List HolChar) →
    Option (Symbol × Locn × List HolChar)
  | 0, _, _, _ => none
  | _ + 1, [], loc, _ => some (.errorS, loc, [])
  | fuel + 1, c :: cs, loc, prefixes =>
      if isSingle c then
        if prefixes.isEmpty then some (.otherS [c], nextLoc 1 loc, cs) else some (.errorS, loc, cs)
      else if isSymbol c then
        let (tail, rest) := readWhile isSymbol cs
        let name := c :: tail
        let symbol := if prefixes.isEmpty then Symbol.otherS name else .longS prefixes.reverse name
        some (symbol, nextLoc name.length loc, rest)
      else if isAlpha c then
        let (tail, rest) := readWhile isAlphaNumPrime cs
        let name := c :: tail
        let loc := nextLoc name.length loc
        match rest with
        | dot :: rest =>
            if dot == 46 then readIdentFuel fuel rest loc (name :: prefixes)
            else some (if prefixes.isEmpty then .otherS name else .longS prefixes.reverse name, loc, dot :: rest)
        | [] => some (if prefixes.isEmpty then .otherS name else .longS prefixes.reverse name, loc, [])
      else some (.errorS, loc, cs)

/-- Read the next source symbol. `none` outside the result signals fuel
exhaustion; `some none` is end of input. -/
def nextSymbolFuel : Nat → List HolChar → Locn → Option (Option (Symbol × Locs × List HolChar))
  | 0, _, _ => none
  | _ + 1, [], _ => some none
  | fuel + 1, c :: cs, loc => do
      if c == 10 then return ← nextSymbolFuel fuel cs (nextLine loc)
      if isSpace c then return ← nextSymbolFuel fuel cs (nextLoc 1 loc)
      if isDigit c then
        match c.toNat, cs with
        | 48, w :: rest =>
          if w == 119 then
            match rest with
            | [] => return some (.errorS, .locs loc loc, [])
            | first :: tail =>
                if isDigit first then
                  let (digits, rest) := readWhile isDigit (first :: tail)
                  return some (.wordS (number 10 digits), .locs loc (nextLoc (digits.length + 1) loc), rest)
                else if first == 120 then
                  let (digits, rest) := readWhile isHex tail
                  return some (.wordS (number 16 digits), .locs loc (nextLoc (digits.length + 2) loc), rest)
                else return some (.errorS, .locs loc loc, rest)
          else if w == 120 then
            let (digits, rest) := readWhile isHex rest
            return some (.numberS (Int.ofNat (number 16 digits)), .locs loc (nextLoc digits.length loc), rest)
          else
            let (digits, rest) := readWhile isDigit cs
            return some (.numberS (Int.ofNat (number 10 (c :: digits))), .locs loc (nextLoc digits.length loc), rest)
        | _, _ =>
          let (digits, rest) := readWhile isDigit cs
          return some (.numberS (Int.ofNat (number 10 (c :: digits))), .locs loc (nextLoc digits.length loc), rest)
      if c == 126 && (cs.head?.map isDigit).getD false then
        let (digits, rest) := readWhile isDigit cs
        return some (.numberS (-(Int.ofNat (number 10 digits))), .locs loc (nextLoc (digits.length + 1) loc), rest)
      if c == 39 then
        let (digits, rest) := readWhile isAlphaNumPrime cs
        return some (.otherS (c :: digits), .locs loc (nextLoc digits.length loc), rest)
      if c == 34 then
        let (sym, stop, rest) ← readStringFuel fuel cs [] (nextLoc 1 loc)
        return some (sym, .locs loc stop, rest)
      match c.toNat, cs with
      | 42, 41 :: rest => return some (.errorS, .locs loc (nextLoc 2 loc), rest)
      | 35, 34 :: rest =>
          let (sym, stop, rest) ← readStringFuel fuel rest [] (nextLoc 2 loc)
          let sym := match sym with | .stringS [x] => Symbol.charS x | _ => .errorS
          return some (sym, .locs loc stop, rest)
      | 35, 40 :: rest =>
          let (sym, stop, rest) ← readFfiFuel fuel rest [] (nextLoc 2 loc)
          return some (sym, .locs loc stop, rest)
      | 40, 42 :: rest =>
          match ← skipCommentFuel fuel rest 0 (nextLoc 2 loc) with
          | none => return some (.errorS, .locs loc (nextLoc 2 loc), [])
          | some (rest, loc) => return ← nextSymbolFuel fuel rest loc
      | 95, rest => return some (.otherS [95], .locs loc loc, rest)
      | _, _ =>
          let (sym, stop, rest) ← readIdentFuel fuel (c :: cs) loc []
          return some (sym, .locs loc stop, rest)

/-- Lex a complete byte stream. The original's end-position convention is
preserved; explicit fuel exhaustion fails instead of returning partial tokens. -/
def lexFuel : Nat → List HolChar → Locn → Option (List (Token × Locs))
  | 0, _, _ => none
  | fuel + 1, input, loc => do
      match ← nextSymbolFuel fuel input loc with
      | none => pure []
      | some (sym, .locs start stop, rest) =>
          pure ((tokenOfSymbol sym, .locs start stop) :: (← lexFuel fuel rest (nextLoc 1 stop)))

end Flapjack.CakeParser.Lexer
