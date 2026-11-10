module

public import Flapjack.Parser.ParseTree

-- Checks below run compiled code from these modules.
public meta import Flapjack.Parser.Lexer
public meta import Flapjack.Parser.ParseTree
@[expose] public section

namespace Flapjack.Test.ParserMkleafParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:40`, `mkleaf_def`. -/
def keywordGuard : Bool :=
  match P.mkLeaf (.keywordT .skipK, unknownLoc) with
  | [.lf (.keywordT .skipK) loc] => loc == unknownLoc
  | _ => false

def identifierLoc : Locs :=
  { start := .posn 2 3, stop := .posn 2 4 }

def identifierGuard : Bool :=
  match P.mkLeaf (.identT "name", identifierLoc) with
  | [.lf (.identT "name") loc] => loc == identifierLoc
  | _ => false

#eval keywordGuard && identifierGuard
#guard keywordGuard
#guard identifierGuard

end Flapjack.Test.ParserMkleafParity
