import Flapjack.Pancake.Proofs.PanGlobals

/-!
# Shared pan_globals parity fixtures

The empty finite maps, the base state `state0` and the `ml`/`Word8` helpers
shared by the `pan_globals` parity modules.
-/

namespace Flapjack.Test.Fixtures.PanGlobals

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s
abbrev Word8 := RiscV.Word 8

abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL :=
  HolFiniteMapExact.empty

abbrev emptyCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  HolFiniteMapExact.empty

abbrev state0 : PanSemStateFiniteExact 8 Unit :=
  { locals := emptyValues
    globals := emptyValues
    structs := []
    code := emptyCode
    eshapes := emptyShapes
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

end Flapjack.Test.Fixtures.PanGlobals
