import Flapjack.CakeParser.Lexer
import Flapjack.CakeParser.PegEval
import Flapjack.CakeParser.PtreeConversion

/-! A bounded source-to-CakeML-AST entry point. The original parser's detailed
errors and exact continuation-machine fuel are not represented here, and the
conversion workers' fuel bounds remain unproved. -/
namespace Flapjack.CakeParser.Frontend
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
open Flapjack.CakeParser.PegEval Flapjack.CakeParser.PtreeConversion

inductive ParseResult where
  | exhausted
  | rejected
  | success : List Flapjack.AstHOL.Dec → ParseResult

/-- Parse a complete token stream. The entire stream must be consumed, as in
`cmlParse$destResult`; malformed trees are rejected. -/
def parseTokensFuel (fuel : Nat) (tokens : List (Token × Locs)) : ParseResult :=
  match eval fuel (.nt (.inl .nTopLevelDecs) .id) tokens with
  | .exhausted => .exhausted
  | .failure => .rejected
  | .success (pt :: _) [] => match ptreeTopLevelDecs pt with
    | none => .rejected
    | some ds => .success ds
  | .success _ _ => .rejected

/-- Lex and parse source bytes, starting at the original default location. -/
def parseSourceFuel (lexerFuel parserFuel : Nat) (source : List HolChar) : ParseResult :=
  match Lexer.lexFuel lexerFuel source defaultLoc with
  | none => .exhausted
  | some tokens => parseTokensFuel parserFuel tokens

/-- Return the location of the first token left after parsing top-level
declarations. Other parser failures have no location in this bounded
interpreter and therefore return `none`. -/
def unconsumedTokenLocationFuel (lexerFuel parserFuel : Nat) (source : List HolChar) : Option Locs := do
  let tokens ← Lexer.lexFuel lexerFuel source defaultLoc
  match eval parserFuel (.nt (.inl .nTopLevelDecs) .id) tokens with
  | .success _ ((_, loc) :: _) => some loc
  | _ => none

end Flapjack.CakeParser.Frontend
