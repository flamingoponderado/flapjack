import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.LimitVar

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Literal `full_ssa_cc_trans` (`word_allocScript.sml:1822-1828`): set up the
argument renaming from the program's `limit_var`, rename the body with an empty
loop-target list, and prefix the entry move. HOL's `setup_ssa` result width is
independent; here both widths are the program's, as the `Seq` forces. Proof-side
port: the executed list-state SSA pass is not routed through it. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fullSsaCcTrans {width : Nat} [NeZero width] (n : Nat)
    (prog : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  let lim := limitVar prog
  let (mov, ssa, na) := setupSSA (outputWidth := width) n lim prog
  let (prog', _ssa', _na') := ssaCcTrans prog ssa na []
  .seq mov prog'

end Flapjack.Compiler.Backend.WordAlloc
