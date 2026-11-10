module

public import Flapjack.Compiler.Backend.WordBignum.CompileExp

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.WordLang
public meta import Flapjack.Word
public meta import Flapjack.Compiler.Backend.WordBignum.CompileExp
@[expose] public section

/-! Replay the pinned HOL expression-translation probe. -/
namespace Flapjack.Test.WordBignumCompileExpParity
open Flapjack.Compiler.Backend.WordBignum

private abbrev E := Flapjack.WordLangExpHOL (BitVec 64)

#guard match compileExp (.op .add [.var 33, .const 7] : E) with
  | .op .add [.lookup (.temp n), .const w] => n == 1 && w == 7
  | _ => false

#guard match compileExp (.op .add [.var 1] : E) with
  | .const w => w == 0
  | _ => false

#guard match compileExp (.lookup (.temp 3) : E) with
  | .const w => w == 0
  | _ => false

#guard match compileExp (.shift .lsl (.var 2) (.const 3) : E) with
  | .shift .lsl (.lookup (.temp n)) (.const w) => n == 2 && w == 3
  | _ => false

end Flapjack.Test.WordBignumCompileExpParity
