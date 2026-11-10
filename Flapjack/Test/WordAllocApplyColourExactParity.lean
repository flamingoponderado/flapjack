module

public import Flapjack.Compiler.Backend.WordAlloc.Colour
public import Flapjack.RiscV.OracleAllocator

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.WordAlloc.Colour
public meta import Flapjack.RiscV.OracleAllocator
@[expose] public section

/-! Direct HOL parity for the tagged exact `applyColour` (`apply_colour_def`)
    over `WordLangProgHOL (BitVec 64)`. Every row is an original HOL `EVAL`
    observation captured in `scripts/hol-probes/apply_colour_probe.out`; the
    colour function is `total_colour ^colour`, whose values on these fixtures
    (1 ↦ 14, 2 ↦ 2, 3 ↦ 18, 5 ↦ 0, 7 ↦ 0) are separately checked against the
    same probe by `Flapjack.Test.CakeApplyColourParity`. -/

namespace Flapjack.Test.WordAllocApplyColourExactParity

open Flapjack Flapjack.WordAlloc

abbrev P := WordLangProgHOL (BitVec 64)

def aliasColour (n : Nat) : Nat := if n = 0 then 0 else 1

/-- `apply_colour_alias_assign=Assign 1 (Var 1)` -/
def aliasAssignRow : Bool :=
  match applyColour aliasColour (.assign 2 (.var 1) : P) with
  | .assign 1 (.var 1) => true
  | _ => false

#guard aliasAssignRow

/-- `apply_colour_alias_const=Assign 1 (Const 5w)` -/
def aliasConstRow : Bool :=
  match applyColour aliasColour (.assign 2 (.const 5) : P) with
  | .assign 1 (.const w) => w == 5
  | _ => false

#guard aliasConstRow

end Flapjack.Test.WordAllocApplyColourExactParity
