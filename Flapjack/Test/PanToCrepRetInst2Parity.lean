import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport

/-! Direct-HOL `evaluate_shape_invariant_ret_inst2` regression. The paired
`scripts/hol-probes/pan_to_crep_ret_inst2_probe.out` records all five HOL
premises for an empty-argument call whose body returns word 7. -/

namespace Flapjack.Test.PanToCrepRetInst2Parity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev Width := 8
private abbrev Word := BitVec Width

private def sourceName : MlS := Flapjack.Basis.Pure.MlString.ofString "f"
private def resultWord : Word := BitVec.ofNat Width 7
private def returnBody : ProgHOL Width := .return (.const resultWord)

private def ffiState : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed
    ffiState := ()
    ioEvents := [] }

private def sourceState : PanSemStateFiniteExact Width Unit :=
  { locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    structs := []
    code := (HolFiniteMapExact.empty : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL Width × ShapeHOL)).update
        (sourceName, ([], returnBody, .one))
    eshapes := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 2
    be := false
    ffi := ffiState
    baseAddr := 0
    topAddr := 0 }

private def targetState : CrepSemHOLState Width Unit :=
  { locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 2
    be := false
    ffi := ffiState
    baseAddr := 0
    topAddr := 0 }

private def context : PanToCrepContextExact Width :=
  { vars := HolFiniteMapExact.empty
    funcs := HolFiniteMapExact.empty
    eids := HolFiniteMapExact.empty
    vmax := 0 }

private def targetLocals : HolFiniteMapExact Nat (HolWordLab Width) :=
  HolFiniteMapExact.empty

private def bodyEntry : PanSemStateFiniteExact Width Unit :=
  {sourceState.decClockHOLFinite with locals := HolFiniteMapExact.empty}

private noncomputable def bodyOutput :=
  PanSemStateFiniteExact.evaluateHOLFiniteState bodyEntry returnBody

private theorem fivePremises :
    evalListHOLFiniteClassical sourceState [] = some [] ∧
    Flapjack.lookupCodeHOLExact sourceState.code.lookup sourceName [] =
      some (returnBody, (fun _ => none), ShapeHOL.one) ∧
    bodyOutput = (some (.returned (.val (.word resultWord))), bodyOutput.2) ∧
    panToCrepStateRelFiniteExact sourceState targetState ∧
    panToCrepLocalsRelFiniteExact context sourceState.locals targetLocals := by
  constructor
  · classical
    simp [evalListHOLFiniteClassical, PanSemStateFiniteExact.evalListHOLFinite,
      Flapjack.evalListHOLExact]
  constructor
  · simp [Flapjack.lookupCodeHOLExact, sourceState, sourceName, returnBody,
      FUPDATE, HolFiniteMapExact.empty, HolFiniteMapExact.update]
  constructor
  · classical
    apply Prod.ext
    · simp [bodyOutput, bodyEntry, PanSemStateFiniteExact.evaluateHOLFiniteState,
      PanSemStateFiniteExact.evaluateHOLFiniteStateWithDeciders,
      PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
      returnBody, resultWord, sourceState, ffiState, HolFiniteMapExact.empty,
      HolFiniteMapExact.update, Flapjack.evalHOLExact, shapeOfHOLExact]
    · rfl
  constructor
  · simp [panToCrepStateRelFiniteExact, sourceState, targetState, ffiState,
      HolFiniteMapExact.empty, HolFiniteMapExact.update]
  · simp [panToCrepLocalsRelFiniteExact, noOverlapFiniteExact,
      ctxtMaxFiniteExact, context, sourceState, targetLocals, ffiState,
      HolFiniteMapExact.empty]

theorem returnShapeInvariantFixture :
    isWfShapeValueHOLExact ([] : StructContextExact) (.val (.word resultWord)) = true := by
  have h := panToCrepFiniteEvaluateShapeInvariantRetInst2
    (arguments := []) (source := sourceState) (fname := sourceName)
    (values := []) (lookupBody := returnBody)
    (newlocals := HolFiniteMapExact.empty) (returnShape := .one)
    (program := returnBody) (result := .returned (.val (.word resultWord)))
    (postState := bodyOutput.2) (target := targetState)
    (relationContext := context) (targetLocals := targetLocals)
    (hargs := fivePremises.1)
    (hlookup := fivePremises.2.1)
    (hbody := by exact fivePremises.2.2.1)
    (hstate := fivePremises.2.2.2.1)
    (hlocals := fivePremises.2.2.2.2)
  simpa [resultWord] using h

end Flapjack.Test.PanToCrepRetInst2Parity
