import Flapjack.CakeParser.Lexer

/-! CakeML's top-level semicolon grouping over the functional lexer output. -/
namespace Flapjack.CakeParser.LexerImpl
open Flapjack.Misc.Location

/-- Collect tokens through the first semicolon at nesting depth zero. -/
@[hol "cakeml/compiler/parsing/lexer_implScript.sml" "lex_aux_tokens_def"]
def lexAuxTokens (acc : List (Token × Locs)) (depth : Nat) : List (Token × Locs) →
    Option (List (Token × Locs) × List (Token × Locs))
  | [] => none
  | (token, loc) :: rest =>
      let acc := (token, loc) :: acc
      if token == .semicolonT && depth == 0 then some (acc.reverse, rest)
      else
        let depth := match token with
          | .letT | .structT | .sigT | .lparT => depth + 1
          | .endT | .rparT => depth - 1
          | _ => depth
        lexAuxTokens acc depth rest

/-- Produce complete top-level chunks; incomplete trailing tokens are dropped
as in the original. Fuel exhaustion is reported separately. -/
def lexAllTokensFuel : Nat → List (Token × Locs) → Option (List (List (Token × Locs)))
  | 0, _ => none
  | fuel + 1, input =>
      match lexAuxTokens [] 0 input with
      | none => some []
      | some (chunk, rest) => do pure (chunk :: (← lexAllTokensFuel fuel rest))

end Flapjack.CakeParser.LexerImpl
