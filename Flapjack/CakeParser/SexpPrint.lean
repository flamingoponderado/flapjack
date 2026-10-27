import Flapjack.CakeParser.Sexp

/-! Byte-oriented S-expression rendering for the CakeML `--print_sexp` path.
This is infrastructure for the AST encoder: the executable does not yet use
it, and correspondence with HOL's printer has not been proved. -/
namespace Flapjack.CakeParser.Sexp
open Flapjack.Basis.Pure.MlString

private def ascii (s : String) : List HolChar := (ofString s).explode

private def escape : List HolChar → List HolChar
  | [] => []
  | c :: cs =>
    (if c.toNat == 34 || c.toNat == 92 then [BitVec.ofNat 8 92] else []) ++
      [c] ++ escape cs

mutual
/-- Render an S-expression using the original printer's list and quote syntax. -/
def render (sexp : Sexp) : List HolChar :=
  match sexp with
  | .sym bytes => bytes
  | .num n => ascii (toString n)
  | .str bytes => ascii "\"" ++ escape bytes ++ ascii "\""
  | .cons (.sym name) (.cons quoted (.sym terminator)) =>
    if name == ascii "quote" && terminator == ascii "nil" then
      ascii "'" ++ render quoted
    else ascii "(" ++ name ++ renderTail (.cons quoted (.sym terminator))
  | .cons head tail => ascii "(" ++ render head ++ renderTail tail
termination_by sizeOf sexp

private def renderTail (sexp : Sexp) : List HolChar :=
  match sexp with
  | .sym name => if name == ascii "nil" then ascii ")" else ascii " . " ++ name ++ ascii ")"
  | .cons head tail => ascii " " ++ render head ++ renderTail tail
  | .num n => ascii " . " ++ ascii (toString n) ++ ascii ")"
  | .str bytes => ascii " . \"" ++ escape bytes ++ ascii "\")"
termination_by sizeOf sexp
end

end Flapjack.CakeParser.Sexp
