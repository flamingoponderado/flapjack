import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.RiscV.Model
import Flapjack.Test.PanValueFfiCore

/-! Regression cases paired with
`scripts/hol-probes/pan_structs_compile_correct_probe.out` and
`scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`. -/

namespace Flapjack.Test

open Flapjack

example :
    panStructConvertValue
      (.nStruct "Pair" [("left", .word 3), ("right", .word 5)]) =
        .rStruct [.word 3, .word 5] := by
  simp [panStructConvertValue, panStructConvertFieldValues]

/-! Initial-state byte-range discharge for the `pan_structs`-converted production
state (bead `flapjack-pxn.18.4.3.77.2.15.6`). The conversion rewrites every
`.nStruct` into a name-free `.rStruct`, so a converted value is byte-ranged
unconditionally; only the converted state is claimed, not the raw source state. -/
example :
    PanValueByteRanged (panStructConvertValue
      (.nStruct "Pair" [("left", .word (3 : BitVec 64))] : PanValue (BitVec 64))) :=
  panValueByteRanged_panStructConvertValue _

example (context : StructPassContext) (state : PanSemState (RiscV.Word 64) (FfiState Unit)) :
    PanSemStateRelExecRanged (panStructConvertState context state) :=
  panSemStateRelExecRanged_panStructConvertState context state

/-- Exact-carrier reproduction of the HOL oracle row
    `convert_named_record=RStruct [ValWord 3w; ValWord 5w]` in
    `scripts/hol-probes/pan_structs_compile_correct_probe.out`: the tagged exact
    `convertV` over `ValueHOL` both evaluates the row and agrees with the
    executable `panStructConvertValue` through the checked production bridge. -/
def exactConvertNamedRecord : ValueHOL 64 :=
  .nStruct (Flapjack.Basis.Pure.MlString.ofString "Pair")
    [(Flapjack.Basis.Pure.MlString.ofString "left", .val (.word (BitVec.ofNat 64 3))),
     (Flapjack.Basis.Pure.MlString.ofString "right", .val (.word (BitVec.ofNat 64 5)))]

example :
    convertV exactConvertNamedRecord =
      .rStruct [.val (.word (BitVec.ofNat 64 3)),
        .val (.word (BitVec.ofNat 64 5))] := by
  simp [exactConvertNamedRecord, convertV]

example (context : StructPassContext) :
    structCompileProg context (.skip : Prog Nat) = .skip := by
  exact panStructCompileSkip_eq_skip context

private abbrev Word64 := Flapjack.RiscV.Word 64

def finiteMapRuntime : PanSemState Word64 (FfiState Unit) where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := []
  exceptionShapes := fun _ => none
  memory := fun _ => none
  memaddrs := fun _ => false
  sharedMemaddrs := fun _ => false
  clock := 3
  be := false
  ffi := statefulTestFfiState
  baseAddress := BitVec.ofNat 64 0
  topAddress := BitVec.ofNat 64 100

def finiteMapContext : StructPassContext where
  structs := []
  locals := [("local", .one)]
  globals := [("global", .one)]

def emptyStructCompileContext : StructPassContext where
  structs := []
  locals := []
  globals := []

/-! Paired concrete Load row for
    `compile_exp_correct_load=(Comb [One; One],Comb [One; One],T,T,T)` in
    `pan_structs_compile_exp_correct_probe.out`. -/
def loadCompileCaseRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 3))
      else if address == BitVec.ofNat 64 1 then some (.word (BitVec.ofNat 64 5))
      else none
    memaddrs := fun address =>
      address == BitVec.ofNat 64 0 || address == BitVec.ofNat 64 1 }

def loadCompileCaseValue : PanValue Word64 :=
  .rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]

def loadCompileCaseExpression : Exp Word64 :=
  .load (.comb [.one, .one]) (.const (BitVec.ofNat 64 0))

def loadCompileCaseOutOfDomainRuntime : PanSemState Word64 (FfiState Unit) :=
  { loadCompileCaseRuntime with
    memaddrs := fun address => address == BitVec.ofNat 64 1 }

def loadCompileCaseOutOfDomainMemoryAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel
    loadCompileCaseOutOfDomainRuntime.memaddrs
    loadCompileCaseOutOfDomainRuntime.sharedMemaddrs
    loadCompileCaseOutOfDomainRuntime.be

/-! The paired HOL row
    `compile_exp_correct_load_out_of_domain=(Comb [One; One],Comb [One; One],T,F,F)`
    checks that excluding the base address makes both source and converted
    loads fail, while shape and field-validity checks remain true. -/
example :
    structOldExpShape emptyStructCompileContext loadCompileCaseExpression =
        .comb [.one, .one] ∧
    panSemShapeOf loadCompileCaseValue = .comb [.one, .one] ∧
    panStructValueFieldsOkBool loadCompileCaseOutOfDomainRuntime.structs
      loadCompileCaseValue = true ∧
    evalPanValueExpFull loadCompileCaseOutOfDomainRuntime.structs
      loadCompileCaseOutOfDomainRuntime.locals loadCompileCaseOutOfDomainRuntime.globals
      loadCompileCaseOutOfDomainRuntime.memory loadCompileCaseOutOfDomainRuntime.baseAddress
      loadCompileCaseOutOfDomainRuntime.topAddress (BitVec.ofNat 64 1)
      loadCompileCaseExpression
      (memoryAccess := some loadCompileCaseOutOfDomainMemoryAccess) = none ∧
    evalPanValueExpFull
      (panStructConvertState emptyStructCompileContext
        loadCompileCaseOutOfDomainRuntime).structs
      (panStructConvertState emptyStructCompileContext
        loadCompileCaseOutOfDomainRuntime).locals
      (panStructConvertState emptyStructCompileContext
        loadCompileCaseOutOfDomainRuntime).globals
      (panStructConvertState emptyStructCompileContext
        loadCompileCaseOutOfDomainRuntime).memory
      (panStructConvertState emptyStructCompileContext
        loadCompileCaseOutOfDomainRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext
        loadCompileCaseOutOfDomainRuntime).topAddress (BitVec.ofNat 64 1)
      (structCompileExp emptyStructCompileContext loadCompileCaseExpression)
      (memoryAccess := some loadCompileCaseOutOfDomainMemoryAccess) = none := by
  simp [loadCompileCaseOutOfDomainRuntime, loadCompileCaseOutOfDomainMemoryAccess,
    loadCompileCaseRuntime, loadCompileCaseExpression, loadCompileCaseValue,
    emptyStructCompileContext, finiteMapRuntime, evalPanValueExpFull,
    structOldExpShape, panSemShapeOf, panStructValueFieldsOkBool,
    panStructValuesFieldsOkBool,
    panValueMemoryAccessOfModel, RiscV.panRiscVMemoryModel,
    panValueFlatLoad, panValueFlatLoadFuel, panValueFlatLoadListFuel,
    panValueFlatReadWord, panValueFlatOffset, panValueFlatContextFuel,
    panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel,
    shapeSizeWithContext, isWfShape, isWfShape.isWfShapeList,
    structCompileShapeWF, structCompileShapeWF.structCompileShapesWF,
    panStructConvertState, structCompileExp, structCompileShape]

/-! Paired LoadByte constructor regressions for the direct HOL-EVAL success
row `compile_exp_correct_load_byte` and the out-of-domain failure row in
`pan_structs_compile_exp_correct_probe.out`. -/
def loadByteCompileCaseRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 19))
      else none
    memaddrs := fun address => address == BitVec.ofNat 64 0 }

def loadByteCompileCaseMemoryAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel
    loadByteCompileCaseRuntime.memaddrs
    loadByteCompileCaseRuntime.sharedMemaddrs loadByteCompileCaseRuntime.be

def loadByteCompileCaseOutOfDomainRuntime : PanSemState Word64 (FfiState Unit) :=
  { loadByteCompileCaseRuntime with memaddrs := fun _ => false }

def loadByteCompileCaseOutOfDomainMemoryAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel
    loadByteCompileCaseOutOfDomainRuntime.memaddrs
    loadByteCompileCaseOutOfDomainRuntime.sharedMemaddrs
    loadByteCompileCaseOutOfDomainRuntime.be

def loadByteCompileCaseExpression : Exp Word64 :=
  .loadByte (.const (BitVec.ofNat 64 0))

def loadByteCompileCaseValue : PanValue Word64 :=
  .word (BitVec.ofNat 64 19)

#guard
  let source := evalPanValueExpFull
    loadByteCompileCaseRuntime.structs loadByteCompileCaseRuntime.locals
    loadByteCompileCaseRuntime.globals loadByteCompileCaseRuntime.memory
    loadByteCompileCaseRuntime.baseAddress loadByteCompileCaseRuntime.topAddress
    (BitVec.ofNat 64 1) loadByteCompileCaseExpression
    (memoryAccess := some loadByteCompileCaseMemoryAccess)
  let target := evalPanValueExpFull
    (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).structs
    (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).locals
    (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).globals
    (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).memory
    (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).baseAddress
    (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).topAddress
    (BitVec.ofNat 64 1)
    (structCompileExp emptyStructCompileContext loadByteCompileCaseExpression)
    (memoryAccess := some loadByteCompileCaseMemoryAccess)
  panStructShapeEqBool
    (structOldExpShape emptyStructCompileContext loadByteCompileCaseExpression) .one &&
  panStructValueFieldsOkBool loadByteCompileCaseRuntime.structs
    loadByteCompileCaseValue &&
  (match source with
   | some (.word result) => result == BitVec.ofNat 64 19
   | _ => false) &&
  (match target with
   | some (.word result) => result == BitVec.ofNat 64 19
   | _ => false)

#guard
  (evalPanValueExpFull loadByteCompileCaseOutOfDomainRuntime.structs
    loadByteCompileCaseOutOfDomainRuntime.locals
    loadByteCompileCaseOutOfDomainRuntime.globals
    loadByteCompileCaseOutOfDomainRuntime.memory
    loadByteCompileCaseOutOfDomainRuntime.baseAddress
    loadByteCompileCaseOutOfDomainRuntime.topAddress
    (BitVec.ofNat 64 1) loadByteCompileCaseExpression
    (memoryAccess := some loadByteCompileCaseOutOfDomainMemoryAccess)).isNone

/-! The direct HOL oracle row `compile_exp_correct_load32_le_success` uses an
aligned 64-bit word cell and checks that `Load32` extracts the low four bytes.
The same explicit RISC-V memory model is installed in the full evaluator on
both sides of the compile case; its default whole-cell fallback is not used. -/
example : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
    finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
    (.shift .asr (.const (BitVec.ofNat 64 0x8000000000000000))
      (.const (BitVec.ofNat 64 1))) =
    some (.word (BitVec.ofNat 64 0xc000000000000000)) := by
  have hvalid : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 1) <
      PanShiftWidth.width (α := Word64) := by decide
  have hasr : ArithmeticShiftRight.arithmeticShiftRight
      (BitVec.ofNat 64 0x8000000000000000) (BitVec.ofNat 64 1) =
        BitVec.ofNat 64 0xc000000000000000 := by decide
  simp [evalPanValueExpFull, evalPanShiftFull, finiteMapRuntime, hvalid, hasr]

example : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
    finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
    (.shift .ror (.const (BitVec.ofNat 64 0x8000000000000001))
      (.const (BitVec.ofNat 64 1))) =
    some (.word (BitVec.ofNat 64 0xc000000000000000)) := by
  have hvalid : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 1) <
      PanShiftWidth.width (α := Word64) := by decide
  have hror : RotateRightOp.rotateRight
      (BitVec.ofNat 64 0x8000000000000001) (BitVec.ofNat 64 1) =
        BitVec.ofNat 64 0xc000000000000000 := by decide
  simp [evalPanValueExpFull, evalPanShiftFull, finiteMapRuntime, hvalid, hror]

example : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
    finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
    (.shift .lsl (.const (BitVec.ofNat 64 3))
      (.const (BitVec.ofNat 64 64))) = none := by
  have hcutoff : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 64) ≠ 0 ∧
      PanShiftWidth.width (α := Word64) ≤
        PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 64) := by decide
  simp [evalPanValueExpFull, evalPanShiftFull, finiteMapRuntime, hcutoff]

/-! A nested named shape compiles to a nested `Comb`. This checks that the
    target loader's structural fuel covers every list element after alias
    expansion, while the source load walks the same three memory words. -/
def nestedLoadStructContext : StructContext :=
  [ ("Pair", {
      fields := [("inner", .named "Inner"), ("last", .one)]
      size := 3
    }),
    ("Inner", {
      fields := [("left", .one), ("right", .one)]
      size := 2
    }) ]

def nestedLoadCompileContext : StructPassContext :=
  -- Production's HOL context relation observes names and field shapes here,
  -- while the source context supplies the authoritative sizes.
  -- Deliberately skew cached sizes to guard against accidentally requiring
  -- full StructInfo equality in the compiled-load conversion.
  { structs :=
      [("Pair", { fields := [("inner", .named "Inner"), ("last", .one)], size := 99 }),
       ("Inner", { fields := [("left", .one), ("right", .one)], size := 98 })]
    locals := [], globals := [] }

def nestedLoadRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    structs := nestedLoadStructContext
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 7))
      else if address == BitVec.ofNat 64 1 then some (.word (BitVec.ofNat 64 11))
      else if address == BitVec.ofNat 64 2 then some (.word (BitVec.ofNat 64 13))
      else none
    memaddrs := fun address => address == BitVec.ofNat 64 0 ||
      address == BitVec.ofNat 64 1 || address == BitVec.ofNat 64 2 }

def nestedLoadExpression : Exp Word64 :=
  .load (.named "Pair") (.const (BitVec.ofNat 64 0))

def nestedLoadSourceValue : PanValue Word64 :=
  .nStruct "Pair"
    [("inner", .nStruct "Inner"
      [("left", .word (BitVec.ofNat 64 7)), ("right", .word (BitVec.ofNat 64 11))]),
     ("last", .word (BitVec.ofNat 64 13))]

def nestedLoadConvertedValue : PanValue Word64 :=
  .rStruct [
    .rStruct [.word (BitVec.ofNat 64 7), .word (BitVec.ofNat 64 11)],
    .word (BitVec.ofNat 64 13)]

example :
    structOldExpShape nestedLoadCompileContext nestedLoadExpression = .named "Pair" ∧
    panSemShapeOf nestedLoadSourceValue = .named "Pair" ∧
    panStructValueFieldsOkBool nestedLoadRuntime.structs nestedLoadSourceValue = true ∧
    structCompileShapeWF nestedLoadStructContext (.named "Pair") =
      .comb [.comb [.one, .one], .one] ∧
    evalPanValueExp nestedLoadRuntime.structs nestedLoadRuntime.locals
      nestedLoadRuntime.globals nestedLoadRuntime.memory nestedLoadRuntime.baseAddress
      nestedLoadRuntime.topAddress (BitVec.ofNat 64 1) nestedLoadExpression =
      some nestedLoadSourceValue ∧
    evalPanValueExp [] nestedLoadRuntime.locals nestedLoadRuntime.globals
      nestedLoadRuntime.memory nestedLoadRuntime.baseAddress nestedLoadRuntime.topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp nestedLoadCompileContext nestedLoadExpression) =
      some nestedLoadConvertedValue := by
  have hcompiled : structCompileShapeWF nestedLoadStructContext (.named "Pair") =
      .comb [.comb [.one, .one], .one] := by
    simp [structCompileShapeWF, structCompileShapeWF.structCompileShapesWF,
      nestedLoadStructContext, lookupInfoWithRest]
  constructor
  · simp [structOldExpShape, nestedLoadCompileContext, nestedLoadExpression]
  constructor
  · simp [panSemShapeOf, nestedLoadSourceValue]
  constructor
  · simp [panStructValueFieldsOkBool, panStructFieldValuesFieldsOkBool,
      nestedLoadRuntime, nestedLoadStructContext, nestedLoadSourceValue,
      panValueFieldsHaveShapes, panValueShape, panShapeMatches, lookupInfo]
  constructor
  · exact hcompiled
  constructor
  · simp [nestedLoadRuntime, nestedLoadStructContext, nestedLoadExpression,
      nestedLoadSourceValue, finiteMapRuntime, evalPanValueExp,
      panValueFlatLoad, panValueFlatLoadFuel, panValueFlatLoadFieldsFuel,
      panValueFlatReadWord, panValueFlatOffset,
      panValueFlatContextFuel, panValueFlatShapeFuel,
      panValueFlatFieldsFuel,
      shapeSizeWithContext, isWfShape, lookupInfoWithRest, lookupInfo]
  · have hcompiledExpression :
      structCompileExp nestedLoadCompileContext nestedLoadExpression =
          .load (.comb [.comb [.one, .one], .one]) (.const (BitVec.ofNat 64 0)) := by
      simp [structCompileExp, structCompileShape, nestedLoadCompileContext,
        nestedLoadExpression, structCompileShapeWF,
        structCompileShapeWF.structCompileShapesWF, lookupInfoWithRest]
    rw [hcompiledExpression]
    simp [nestedLoadRuntime, nestedLoadStructContext, nestedLoadConvertedValue,
      finiteMapRuntime, evalPanValueExp, panValueFlatLoad, panValueFlatLoadFuel,
      panValueFlatLoadListFuel, panValueFlatReadWord, panValueFlatOffset,
      panValueFlatContextFuel, panValueFlatShapeFuel,
      panValueFlatShapeFuel.panValueFlatShapeListFuel, shapeSizeWithContext,
      isWfShape, isWfShape.isWfShapeList]

def pairCompileInfo : StructInfo where
  fields := [("left", .one), ("right", .one)]
  size := 2

def namedStructRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with structs := [("Pair", pairCompileInfo)] }

def namedStructCompileContext : StructPassContext :=
  { emptyStructCompileContext with structs := [("Pair", pairCompileInfo)] }

def nstructCompileCaseValue : PanValue Word64 :=
  .nStruct "Pair"
    [("left", .word (BitVec.ofNat 64 3)),
     ("right", .word (BitVec.ofNat 64 5))]

def nfieldCompileRuntime : PanSemState Word64 (FfiState Unit) :=
  { namedStructRuntime with
    locals := fun name => if name == "record" then some nstructCompileCaseValue else none }

def nfieldCompileContext : StructPassContext :=
  { namedStructCompileContext with locals := [("record", .named "Pair")] }

def nfieldCompileExpression : Exp Word64 :=
  .nField "right" (.var .local "record")

/-! Paired guard for the direct HOL-EVAL row
`compile_exp_correct_nfield=(One,One,T,T,T)` in
`scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`. The Lean case
uses the full evaluator on source and converted states with no extra memory
model. -/
#guard
  let source := evalPanValueExpFull
    nfieldCompileRuntime.structs nfieldCompileRuntime.locals
    nfieldCompileRuntime.globals nfieldCompileRuntime.memory
    nfieldCompileRuntime.baseAddress nfieldCompileRuntime.topAddress
    (BitVec.ofNat 64 8) nfieldCompileExpression (memoryAccess := none)
  let target := evalPanValueExpFull
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).structs
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).locals
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).globals
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).memory
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).baseAddress
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).topAddress
    (BitVec.ofNat 64 8)
    (structCompileExp nfieldCompileContext nfieldCompileExpression)
    (memoryAccess := none)
  panStructShapeEqBool
    (structOldExpShape nfieldCompileContext nfieldCompileExpression) .one &&
  panStructValueFieldsOkBool nfieldCompileRuntime.structs
    (.word (BitVec.ofNat 64 5)) &&
  (match source with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false) &&
  (match target with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false)

def rfieldCompileCaseValue : PanValue Word64 :=
  .rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]

def rfieldCompileRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    locals := fun name => if name == "tuple" then some rfieldCompileCaseValue else none }

def rfieldCompileContext : StructPassContext :=
  { emptyStructCompileContext with locals := [("tuple", .comb [.one, .one])] }

def rfieldCompileExpression : Exp Word64 :=
  .rField 1 (.var .local "tuple")

/-! Paired guard for the direct HOL-EVAL row
`compile_exp_correct_rfield=(One,One,T,T,T)` in
`scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`. The Lean case
uses the full evaluator on source and converted states with no extra memory
model. -/
#guard
  let source := evalPanValueExpFull
    rfieldCompileRuntime.structs rfieldCompileRuntime.locals
    rfieldCompileRuntime.globals rfieldCompileRuntime.memory
    rfieldCompileRuntime.baseAddress rfieldCompileRuntime.topAddress
    (BitVec.ofNat 64 8) rfieldCompileExpression (memoryAccess := none)
  let target := evalPanValueExpFull
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).structs
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).locals
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).globals
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).memory
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).baseAddress
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).topAddress
    (BitVec.ofNat 64 8)
    (structCompileExp rfieldCompileContext rfieldCompileExpression)
    (memoryAccess := none)
  panStructShapeEqBool
    (structOldExpShape rfieldCompileContext rfieldCompileExpression) .one &&
  panStructValueFieldsOkBool rfieldCompileRuntime.structs
    (.word (BitVec.ofNat 64 5)) &&
  (match source with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false) &&
  (match target with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false)

def finiteMapState : PanStructFiniteState Word64 (FfiState Unit) :=
  panStructFiniteStateFromMaps finiteMapRuntime
    [("local", .word (BitVec.ofNat 64 7))]
    [("global", .word (BitVec.ofNat 64 11))] [("E", .one)]
    [("f", ([], .skip, .one))]
    (by simp) (by simp) (by simp) (by simp)

def finiteMapStateAtClock (clock : Nat) :
    PanStructFiniteState Word64 (FfiState Unit) :=
  { finiteMapState with
    runtime := { finiteMapState.runtime with clock := clock } }

example : finiteMapState.runtime.locals "local" =
    some (.word (BitVec.ofNat 64 7)) := by
  rfl

example : finiteMapState.runtime.globals "global" =
    some (.word (BitVec.ofNat 64 11)) := by
  rfl

example : finiteMapState.runtime.exceptionShapes "E" = some .one := by
  rfl

example : finiteMapState.runtime.locals "local" =
    panPropsALookupEq "local" finiteMapState.locals := by
  exact finiteMapState.locals_lookup "local"

example : lookupInfo "f" finiteMapState.runtime.code =
    panPropsALookupEq "f" finiteMapState.runtime.code := by
  exact lookupInfo_eq_panPropsALookupEq "f" finiteMapState.runtime.code

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).locals =
      [("local", .word (BitVec.ofNat 64 7))] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertValue]

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).globals =
      [("global", .word (BitVec.ofNat 64 11))] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertValue]

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).exceptionShapes =
      [("E", .one)] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, structCompileShape, structCompileShapeWF]

example :
    lookupInfo "f" (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.code =
      some ([], .skip, .one) := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertState, panStructConvertCode,
    structCompileShape, structCompileShapeWF, lookupInfo]

example :
    ((panStructConvertFiniteState finiteMapContext finiteMapState).runtime.locals
        "local",
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.globals
        "global",
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.exceptionShapes
        "E") =
      (some (.word (BitVec.ofNat 64 7)),
        some (.word (BitVec.ofNat 64 11)), some .one) := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertState, panStructConvertValue,
    panPropsALookupEq, structCompileShape, structCompileShapeWF]

example :
    panSemEvaluateCodeStateWithPostState (memoryAccess := none) statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.skip : Prog Word64) =
      some ((.control (.normal finiteMapState.runtime.locals finiteMapState.runtime.globals
          finiteMapState.runtime.memory finiteMapState.runtime.ffi),
          finiteMapState.runtime.clock), finiteMapState.runtime) := by
  exact panSemEvaluateCodeStateWithPostState_skip statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime

example :
    panSemEvaluateCodeStateWithPostState (memoryAccess := none) statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8)
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime
        (structCompileProg finiteMapContext (.skip : Prog Word64)) =
      some ((.control (.normal
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.locals
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.globals
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.memory
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.ffi),
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.clock),
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime) := by
  simpa [structCompileProg] using
    (panSemEvaluateCodeStateWithPostState_skip statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime)

/-! These four result/state assertions pair the checked-in HOL `TimeOut` and
`NONE` rows with the concrete production evaluator representation. At clock
zero both source and converted states time out and clear locals. At clock three
both continue with normal control and decrement to clock two, preserving
locals, globals, memory, and FFI state. -/

example :
    panSemEvaluateCodeStateWithPostState (memoryAccess := none) statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.tick : Prog Word64) =
      some ((.control (.normal finiteMapState.runtime.locals finiteMapState.runtime.globals
        finiteMapState.runtime.memory finiteMapState.runtime.ffi), 2),
        { finiteMapState.runtime with clock := 2 }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, finiteMapState,
    panStructFiniteStateFromMaps, finiteMapRuntime]

example :
    panSemEvaluateCodeStateWithPostState (memoryAccess := none) statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext
        (finiteMapStateAtClock 3)).runtime
      (structCompileProg finiteMapContext (.tick : Prog Word64)) =
      some ((.control (.normal
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.locals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.globals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.memory
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.ffi), 2),
        { (panStructConvertFiniteState finiteMapContext
            (finiteMapStateAtClock 3)).runtime with clock := 2 }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, structCompileProg,
    finiteMapStateAtClock, finiteMapState, panStructFiniteStateFromMaps,
    finiteMapRuntime, panStructConvertFiniteState, panStructConvertState,
    panStructConvertCode, structCompileShape,
    structCompileShapeWF]

example :
    panSemEvaluateCodeStateWithPostState (memoryAccess := none) statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (finiteMapStateAtClock 0).runtime (.tick : Prog Word64) =
      some ((.timeout (fun _ => none) (finiteMapStateAtClock 0).runtime.globals
        (finiteMapStateAtClock 0).runtime.memory (finiteMapStateAtClock 0).runtime.ffi, 0),
        { (finiteMapStateAtClock 0).runtime with locals := fun _ => none }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, finiteMapStateAtClock,
    finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime]

example :
    panSemEvaluateCodeStateWithPostState (memoryAccess := none) statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext
        (finiteMapStateAtClock 0)).runtime
      (structCompileProg finiteMapContext (.tick : Prog Word64)) =
      some ((.timeout (fun _ => none)
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.globals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.memory
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.ffi, 0),
        { (panStructConvertFiniteState finiteMapContext
            (finiteMapStateAtClock 0)).runtime with locals := fun _ => none }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, structCompileProg,
    finiteMapStateAtClock, finiteMapState, panStructFiniteStateFromMaps,
    finiteMapRuntime, panStructConvertFiniteState, panStructConvertState,
    panStructConvertCode, structCompileShape,
    structCompileShapeWF]

end Flapjack.Test
