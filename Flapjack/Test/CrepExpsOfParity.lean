import Flapjack.Pancake.Semantics.CrepProps

/-!
# Original-domain parity for `crepProps$exps_of`

The expected values are derived from the direct HOL equations of
`cakeml/pancake/semantics/crepPropsScript.sml:1282-1299`, and the probe source
`scripts/hol-probes/crep_exps_of_probeScript.sml` records them for regeneration
with `scripts/hol-probes/regenerate.sh` in a checkout with built CakeML HOL
theories.

The tagged exact `crepExpsOfHOL` is checked both against explicit expected
lists (mapped through `crepExpOfHOL` to the production expression carrier) and
against the production `crepExpsOf` mirror through the `crepProgOfHOL` codec.
-/

namespace Flapjack.Test.CrepExpsOfParity

open Flapjack
open Flapjack.Basis.Pure.MlString

/-- Map the exact expression list onto the production carrier so the expected
lists can use the production `CrepExp` constructors and `BEq`. -/
def mapExps {width : Nat} [NeZero width] (exps : List (CrepExpHOL width)) :
    List (CrepExp (BitVec width)) :=
  exps.map crepExpOfHOL

/-- `Dec`, `Seq`, `Assign` and the `Store`/`StoreGlob`/`ShMem` operands. -/
def parityGuard : Bool :=
  mapExps (crepExpsOfHOL (width := 64)
      (.dec 1 (.const 1) (.seq (.assign 2 (.var 1)) (.assign 3 (.const 2))))) ==
    [.const 1, .var 1, .const 2] &&
  mapExps (crepExpsOfHOL (width := 64)
      (.ite (.var 3) (.store (.var 1) (.var 2)) .skip)) ==
    [.var 3, .var 1, .var 2] &&
  mapExps (crepExpsOfHOL (width := 64) (.while (.const 1) (.assign 2 (.var 1)))) ==
    [.const 1, .var 1] &&
  mapExps (crepExpsOfHOL (width := 64) (.store (.var 1) (.var 2))) ==
    [.var 1, .var 2] &&
  mapExps (crepExpsOfHOL (width := 64) (.store32 (.var 1) (.var 2))) ==
    [.var 1, .var 2] &&
  mapExps (crepExpsOfHOL (width := 64) (.storeByte (.var 1) (.var 2))) ==
    [.var 1, .var 2] &&
  mapExps (crepExpsOfHOL (width := 64) (.storeGlob 1 (.var 7))) ==
    [.var 7] &&
  mapExps (crepExpsOfHOL (width := 64) (.return [.var 1, .const 2])) ==
    [.var 1, .const 2] &&
  mapExps (crepExpsOfHOL (width := 64) (.shMem .load 3 (.var 9))) ==
    [.var 9] &&
  -- The three `Call` cases.
  mapExps (crepExpsOfHOL (width := 64) (.call none (ofString "f") [.var 4, .const 6])) ==
    [.var 4, .const 6] &&
  mapExps (crepExpsOfHOL (width := 64)
      (.call (some ([], none)) (ofString "f") [.var 4])) ==
    [.var 4] &&
  mapExps (crepExpsOfHOL (width := 64)
      (.call (some ([], some (1, .assign 2 (.var 1)))) (ofString "f") [.var 4])) ==
    [.var 4, .var 1] &&
  -- Constructors that contribute nothing.
  mapExps (crepExpsOfHOL (width := 64) .skip) == [] &&
  mapExps (crepExpsOfHOL (width := 64) .tick) == [] &&
  mapExps (crepExpsOfHOL (width := 64) (.extCall (ofString "g") 0 0 0 0)) == []

#eval parityGuard
#guard parityGuard

/-- The exact function and the production mirror agree through the codec. -/
def codecGuard : Bool :=
  mapExps (crepExpsOfHOL (width := 64)
      (.dec 1 (.const 1) (.seq (.assign 2 (.var 1)) (.assign 3 (.const 2))))) ==
    crepExpsOf (crepProgOfHOL (width := 64)
      (.dec 1 (.const 1) (.seq (.assign 2 (.var 1)) (.assign 3 (.const 2))))) &&
  mapExps (crepExpsOfHOL (width := 64)
      (.call (some ([], some (1, .assign 2 (.var 1)))) (ofString "f") [.var 4])) ==
    crepExpsOf (crepProgOfHOL (width := 64)
      (.call (some ([], some (1, .assign 2 (.var 1)))) (ofString "f") [.var 4]))

#eval codecGuard
#guard codecGuard

def runChecks : IO Bool := do
  if parityGuard && codecGuard then
    IO.println "PASS crepProps exps_of HOL rows + codec agreement"
  else
    IO.println "FAIL crepProps exps_of parity"
  pure (parityGuard && codecGuard)

end Flapjack.Test.CrepExpsOfParity
