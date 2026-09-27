import Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase

/-!
# Finite-carrier ShMemLoad case guards

The expected `SOME Error` outcomes are direct HOL `evaluate` rows in
`scripts/hol-probes/pan_sem_store_error_probe.out`:
`shmemload_unbound_result`, `shmemload_domain_result`,
`shmemload_address_eval_failure`, and `shmemload_address_nonword`. The tests
below check those rows against the tagged finite-carrier equation and also
check the result. The tagged case equation itself requires the original state
in all of its error branches.
-/

namespace Flapjack.Test.PanSemShMemLoadCaseParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)
open Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase
open Flapjack.PanSemStateFiniteExact

private abbrev Word8 := RiscV.Word 8
private abbrev ml (name : String) : MlS := Flapjack.Basis.Pure.MlString.ofString name
private abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 8) := HolFiniteMapExact.empty
private abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL := HolFiniteMapExact.empty
private abbrev emptyCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  HolFiniteMapExact.empty

private def baseState : PanSemStateFiniteExact 8 Unit :=
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

private def stateWordX : PanSemStateFiniteExact 8 Unit :=
  { baseState with locals := emptyValues.update (ml "x", .val (.word 3)) }

/-- HOL oracle `shmemload_unbound_result`: destination lookup fails. -/
example :
    (evaluateHOLFiniteState baseState
        (.shMemLoad .op8 .local (ml "z") (.const 0) : ProgHOL 8)).1 = some .error := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
  simp [baseState, evalHOLFinite, evalHOLExact, lookupKvarHOLFinite,
    HolFiniteMapExact.empty]

/-- HOL oracle `shmemload_domain_result`: address and destination are words,
    then the shared-memory domain rejects the load. -/
example :
    (evaluateHOLFiniteState stateWordX
        (.shMemLoad .op8 .local (ml "x") (.const 0) : ProgHOL 8)).1 = some .error := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
  simp [stateWordX, baseState, evalHOLFinite, evalHOLExact, lookupKvarHOLFinite,
    shMemLoadHOLFiniteExact, nbOpHOL,
    HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

/-- HOL oracle `shmemload_address_eval_failure`: evaluation of the address
    returns `NONE`. -/
example :
    (evaluateHOLFiniteState baseState
        (.shMemLoad .op8 .local (ml "x") (.var .local (ml "z")) : ProgHOL 8)).1 =
      some .error := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
  simp [baseState, evalHOLFinite, evalHOLExact, HolFiniteMapExact.empty]

/-- HOL oracle `shmemload_address_nonword`: address evaluation succeeds with a
    non-word value, so the clause returns Error and preserves the state. -/
example :
    (evaluateHOLFiniteState stateWordX
        (.shMemLoad .op8 .local (ml "x") (.rstruct []) : ProgHOL 8)).1 = some .error := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
  simp [stateWordX, baseState, evalHOLFinite, evalHOLExact, HolFiniteMapExact.update,
    HolFiniteMapExact.empty]

end Flapjack.Test.PanSemShMemLoadCaseParity
