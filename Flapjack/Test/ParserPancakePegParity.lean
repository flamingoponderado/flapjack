module

public import Flapjack.Parser

-- Checks below run compiled code from these modules.
public meta import Flapjack.Parser
@[expose] public section

namespace Flapjack.Test.ParserPancakePegParity

open Flapjack Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:137`, `pancake_peg_def`.
    `gTopDecList` is the source-shaped Lean start rule for the PEG record. -/
def parityGuard : Bool :=
  match Parser.parseTopDecs (fun value => value) "exception E : 1;" with
  | .ok [.exnDecl "E" .one] => true
  | _ => false

#eval parityGuard
#guard parityGuard

end Flapjack.Test.ParserPancakePegParity
