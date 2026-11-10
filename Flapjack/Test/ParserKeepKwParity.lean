module

public import Flapjack.Parser.ParseTree

-- Checks below run compiled code from these modules.
public meta import Flapjack.Parser.Lexer
public meta import Flapjack.Parser.ParseTree
@[expose] public section

namespace Flapjack.Test.ParserKeepKwParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:68`, `keep_kw_def`. -/
def keyword : Keyword := .skipK
def token : Token := .keywordT keyword
def other : Token := .keywordT .retK

def successGuard : Bool :=
  match P.keepKw keyword "skip" (PState.ofToks [(token, unknownLoc)]) with
  | (some [.lf actual loc], state) =>
      actual == token && loc == unknownLoc && state.remaining == 0 && state.toks == []
  | _ => false

def mismatchGuard : Bool :=
  match P.keepKw keyword "skip" (PState.ofToks [(other, unknownLoc)]) with
  | (none, state) => state.remaining == 1 && state.toks == [(other, unknownLoc)]
  | _ => false

#eval successGuard && mismatchGuard
#guard successGuard
#guard mismatchGuard

end Flapjack.Test.ParserKeepKwParity
