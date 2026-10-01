import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.RiscV.OracleAllocator

/-! Direct HOL parity for the tagged exact `applyColour` (`apply_colour_def`)
    over `WordLangProgHOL (BitVec 64)`. Every row is an original HOL `EVAL`
    observation captured in `scripts/hol-probes/apply_colour_probe.out`; the
    colour function is `total_colour ^colour`, whose values on these fixtures
    (1 ↦ 14, 2 ↦ 2, 3 ↦ 18, 5 ↦ 0, 7 ↦ 0) are separately checked against the
    same probe by `Flapjack.Test.CakeApplyColourParity`. -/

namespace Flapjack.Test.WordAllocApplyColourExactParity

open Flapjack Flapjack.WordAlloc

def colour : Nat → Nat := wordOracleColour [(1, 7), (3, 9)]

#guard colour 1 == 14 && colour 2 == 2 && colour 3 == 18 && colour 5 == 0 && colour 7 == 0

abbrev P := WordLangProgHOL (BitVec 64)

/-- `apply_colour_assign=Assign 14 (Var 18)` -/
def assignRow : Bool :=
  match applyColour colour (.assign 1 (.var 3) : P) with
  | .assign 14 (.var 18) => true
  | _ => false

#guard assignRow

def aliasColour (n : Nat) : Nat := if n = 0 then 0 else 1

/-- `apply_colour_alias_assign=Assign 1 (Var 1)` -/
def aliasAssignRow : Bool :=
  match applyColour aliasColour (.assign 2 (.var 1) : P) with
  | .assign 1 (.var 1) => true
  | _ => false

#guard aliasAssignRow

/-- `apply_colour_return_raise=Seq (Return 14 [18; 0]) (Raise 0)` -/
def returnRaiseRow : Bool :=
  match applyColour colour (.seq (.return 1 [3, 5]) (.raise 7) : P) with
  | .seq (.return 14 [18, 0]) (.raise 0) => true
  | _ => false

#guard returnRaiseRow

/-- `apply_colour_call_handler=Call (SOME ([14],(⦕ 18 ⦖,⦕ 0 ⦖),Return 14 [18],10,11))
    (SOME 12) [14; 18] (SOME (0,Raise 18,13,14))` -/
def callHandlerRow : Bool :=
  match applyColour colour
      (.call (some ([1], (sptInsert 3 () .ln, sptInsert 5 () .ln), .return 1 [3], 10, 11))
        (some 12) [1, 3] (some (7, .raise 3, 13, 14)) : P) with
  | .call (some (vs, (normal, exc), .return 14 [18], 10, 11)) (some 12) args
      (some (0, .raise 18, 13, 14)) =>
      vs == [14] && (sptToAList normal).map Prod.fst == [18] &&
        (sptToAList exc).map Prod.fst == [0] && args == [14, 18]
  | _ => false

#guard callHandlerRow

/-- `apply_colour_loop_live=Loop ⦕ 0; 14 ⦖ (Assign 14 (Var 18)) ⦕ 18 ⦖` -/
def loopLiveRow : Bool :=
  match applyColour colour
      (.loop (sptInsert 1 () (sptInsert 7 () .ln)) (.assign 1 (.var 3))
        (sptInsert 3 () .ln) : P) with
  | .loop liveIn (.assign 14 (.var 18)) liveOut =>
      ((sptToAList liveIn).map Prod.fst).mergeSort (· ≤ ·) == [0, 14] &&
        (sptToAList liveOut).map Prod.fst == [18]
  | _ => false

#guard loopLiveRow

/-- `apply_colour_alias_const=Assign 1 (Const 5w)` -/
def aliasConstRow : Bool :=
  match applyColour aliasColour (.assign 2 (.const 5) : P) with
  | .assign 1 (.const w) => w == 5
  | _ => false

#guard aliasConstRow

end Flapjack.Test.WordAllocApplyColourExactParity
