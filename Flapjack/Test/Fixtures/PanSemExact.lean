module

public import Flapjack.Pancake.Semantics.PanSem.StateExact
public import Flapjack.Pancake.Semantics.PanSemStateEval

@[expose] public section

/-!
# Shared exact PanSem parity fixtures

The `ml` helper, the concrete `exactState`/`stateA` carriers and the
`isWordValue`/`isErrorKeeping` error projections shared by the exact PanSem
parity modules.
-/

namespace Flapjack.Test.Fixtures.PanSemExact

open Flapjack
open Flapjack.RiscV

/-- The faithful HOL `mlstring` of a source string. -/
abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

abbrev Word8 := RiscV.Word 8

/-- A concrete exact state with `x` a local `7`, `y` a global `9`, clock 5. -/
def exactState : PanSemStateExact 64 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
  globals := fun name => if name = ml "y" then some (.val (.word 9)) else none
  structs := []
  code := fun _ => none
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

/-- A concrete exact state with `x` a local `7`, `g` a global `9`, clock 5. -/
abbrev stateA : PanSemStateExact 8 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
  globals := fun name => if name = ml "g" then some (.val (.word 9)) else none
  structs := []
  code := fun _ => none
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

/-- Word comparison used by the error rows. -/
def isWordValue (expected : Nat) : Option (PanValue (Word 64)) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

/-- Matches an `Error` control result at `clock` whose `x` local is unchanged. -/
def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult (Word 64) Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ => n == clock && isWordValue localValue (locals "x")
      | _ => false
  | _ => false

end Flapjack.Test.Fixtures.PanSemExact
