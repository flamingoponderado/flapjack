module

public import Flapjack.Parser.Grammar

-- Checks below run compiled code from these modules.
public meta import Flapjack.Parser.Lexer
public meta import Flapjack.Parser.Grammar
@[expose] public section

namespace Flapjack.Test.ParserTryProgParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:129`, `try_ProgNT_def`. -/
def closeGuard : Bool :=
  match gTryProg 8 (PState.ofToks [(.rCurT, unknownLoc)]) with
  | (some [.nd .prog [.lf (.keywordT .skipK) loc] nodeLoc], state) =>
      loc == unknownLoc && nodeLoc == unknownLoc &&
      state.remaining == 0 && state.toks == []
  | _ => false

def ordinaryGuard : Bool :=
  match gTryProg 8
      (PState.ofToks [(.keywordT .skipK, unknownLoc), (.semiT, unknownLoc),
        (.rCurT, unknownLoc)]) with
  | (some _, state) => state.remaining == 0
  | _ => false

#eval closeGuard && ordinaryGuard
#guard closeGuard
#guard ordinaryGuard

end Flapjack.Test.ParserTryProgParity
