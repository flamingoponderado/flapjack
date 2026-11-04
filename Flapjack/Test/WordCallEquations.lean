import Flapjack.RiscV.Backend

/-!
Regression coverage for the combined Word call equations.  The callee and
handler are compound programs, which exercises the explicit evaluated-state
boundary instead of relying on a leaf constructor reduction.
-/

namespace Flapjack.RiscV

def wordCallEquationReturnBody : WordProg (Word 8) :=
  .seq .skip (.return 0 [2])

def wordCallEquationRaiseBody : WordProg (Word 8) :=
  .seq .skip (.raise 2)

def wordCallEquationHandlerBody : WordProg (Word 8) :=
  .seq .skip (.return 0 [3])

end Flapjack.RiscV
