import Flapjack.Pancake.Semantics.PanSem.NameDeclBridge

/-! Kernel regressions for the declarator/expression bridge theorems in
`Flapjack.Pancake.Semantics.PanSem.NameDeclBridge`.

The two theorem-application `example`s below are **statement smoke checks**: they
apply the bridge theorems under abstract memory/address premises (`hMem`/`haddr`,
`hargs`) and do not by themselves reproduce any concrete evaluator run.  The
concrete finite-carrier hit/miss witnesses against the direct HOL EVAL rows live
further down (`loadHitState`/`loadMissState`), where `hMem` and `haddr` are
discharged from a literal state.

The expected values are recorded by direct HOL EVAL of the source evaluator in
`scripts/hol-probes/pan_sem_state_eval_probe.out`: the Load rows
`word_load_hit=SOME (ValWord 0x1122334455667788w)` and `word_load_miss=NONE`
(success and memory-domain rejection).  The concrete broad-carrier Lean oracle
guards for those same HOL rows live in `Flapjack/Test/PanSemStateEvalParity.lean`. -/

namespace Flapjack.Test.DeclBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev Word64 := RiscV.Word 64
private abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty
private abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL := HolFiniteMapExact.empty
private abbrev emptyCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  HolFiniteMapExact.empty

private def trivialFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }

/-- A finite state whose domain is exactly `{0}` and whose cell `0` holds `w`. -/
private abbrev loadHitState (w : BitVec 64) : PanSemStateFiniteExact 64 Unit :=
  { locals := emptyValues
    globals := emptyValues
    structs := []
    code := emptyCode
    eshapes := emptyShapes
    memory := fun address => if address = 0 then .word w else .word 0
    memaddrs := fun address => address = 0
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := trivialFfi
    baseAddr := 0
    topAddr := 100 }

/-- The same state with an empty memory domain (`word_load_miss`). -/
private abbrev loadMissState : PanSemStateFiniteExact 64 Unit :=
  { loadHitState 0 with memaddrs := fun _ => False }

/-- The production-side memory function corresponding to `loadHitState w`. -/
private abbrev hitMemory (w : BitVec 64) :
    BitVec 64 → Option (PanValue (BitVec 64)) :=
  fun address => if address = 0 then some (.word w) else none

/-- The production-side memory function corresponding to `loadMissState`. -/
private abbrev missMemory : BitVec 64 → Option (PanValue (BitVec 64)) :=
  fun _ => none

private def noLocals : VarName → Option (PanValue (BitVec 64)) := fun _ => none

private def noGlobals : VarName → Option (PanValue (BitVec 64)) := fun _ => none

private abbrev addressConst : Exp (BitVec 64) := .const (0 : BitVec 64)

private theorem hitMemoryCodecRel (w : BitVec 64) :
    PanValueMemoryCodecRel (hitMemory w) (loadHitState w) := by
  intro address
  by_cases h : address = 0#64
  · simp [hitMemory, h]
  · simp [hitMemory, h]

private theorem missMemoryCodecRel :
    PanValueMemoryCodecRel missMemory loadMissState := by
  intro address
  simp [missMemory]

private theorem addressConstCorrespondence (state : PanSemStateFiniteExact 64 Unit)
    [DecidablePred state.memaddrs] (memory : BitVec 64 → Option (PanValue (BitVec 64)))
    (baseAddress topAddress bytesInWord : BitVec 64) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals memory baseAddress topAddress bytesInWord
        addressConst (memoryAccess := none))
      (state.evalHOLFinite (expToHOL addressConst)) := by
  simp only [PanSemDeclarationValueOptionRel, evalPanValueExp, expToHOL,
    PanSemStateFiniteExact.evalHOLFinite_const, panValueCodecRel_word]

/-- **Concrete finite-carrier witness, success.**  With `w = 0x1122334455667788`
    this is the direct HOL EVAL row `word_load_hit`, here on the tagged finite
    state rather than the broad carrier. -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals (hitMemory 0x1122334455667788)
        0 100 (bytesInWordHOL 64) (.load .one addressConst) (memoryAccess := none))
      ((loadHitState 0x1122334455667788).evalHOLFinite
        (.load .one (expToHOL addressConst))) :=
  evalPanValueExp_load_one_option_correspondence (loadHitState 0x1122334455667788)
    [] noLocals noGlobals (hitMemory 0x1122334455667788) 0 100 (bytesInWordHOL 64)
    addressConst (hitMemoryCodecRel 0x1122334455667788)
    (addressConstCorrespondence (loadHitState 0x1122334455667788) (hitMemory 0x1122334455667788) 0 100 (bytesInWordHOL 64))

/-- **Concrete finite-carrier witness, domain miss.**  Direct HOL EVAL row
    `word_load_miss=NONE`: the memory domain rejects the load, so the relation
    holds with `none` on both sides. -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals missMemory
        0 100 (bytesInWordHOL 64) (.load .one addressConst) (memoryAccess := none))
      (loadMissState.evalHOLFinite (.load .one (expToHOL addressConst))) :=
  evalPanValueExp_load_one_option_correspondence loadMissState
    [] noLocals noGlobals missMemory 0 100 (bytesInWordHOL 64)
    addressConst missMemoryCodecRel
    (addressConstCorrespondence loadMissState missMemory 0 100 (bytesInWordHOL 64))

/-- Statement smoke check: the finite-support Load `.one` bridge under abstract
    memory/address premises.  This exercises the theorem's statement, not a
    concrete evaluator run (see the concrete witnesses above). -/
example (state : PanSemStateFiniteExact 64 Unit) [DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (addressExpression : Exp (RiscV.Word 64))
    (hMem : PanValueMemoryCodecRel memory state)
    (haddr : PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        addressExpression (memoryAccess := none))
      (state.evalHOLFinite (expToHOL addressExpression))) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.load .one addressExpression) (memoryAccess := none))
      (state.evalHOLFinite (.load .one (expToHOL addressExpression))) :=
  evalPanValueExp_load_one_option_correspondence state structs locals globals memory
    baseAddress topAddress bytesInWord addressExpression hMem haddr

/-- Statement smoke check: the executed RV64 `.op` option-level bridge under an
    abstract per-argument premise; not a concrete evaluator run. -/
example (productionState : PanSemState (RiscV.Word 64) Unit)
    (state : PanSemStateFiniteExact 64 Unit) [DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (operator : BinOp) (arguments : List (Exp (RiscV.Word 64)))
    (hargs : ∀ e ∈ arguments,
      PanSemDeclarationValueOptionRel PanValueCodecRel
        (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess productionState)))
        (state.evalHOLFinite (expToHOL e))) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.op operator arguments)
        (memoryAccess := some (panSemBitVec64MemoryAccess productionState)))
      (state.evalHOLFinite (.op operator (arguments.map expToHOL))) :=
  evalPanValueExp_op_option_correspondence_executed productionState state structs locals
    globals memory baseAddress topAddress bytesInWord operator arguments hargs

/-- Offset agreement used by the flat-Load recursion (`flapjack-rdc.2.1.1`). -/
example (address : BitVec 8) (k : Nat) :
    panValueFlatOffset (bytesInWordHOL 8) address k =
      address + bytesInWordHOL 8 * BitVec.ofNat 8 k :=
  panValueFlatOffset_bitvec_add address k

/-- The production state matching `loadHitState`: the source memory is
    unconstrained here (the bridge reads it through `memory`), only the
    `memaddrs` domain must agree with the finite state. -/
private abbrev loadHitProductionState : PanSemState (RiscV.Word 64) Unit :=
  { locals := noLocals
    globals := noGlobals
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun address => address = 0
    sharedMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := ()
    baseAddress := 0
    topAddress := 100 }

private abbrev loadMissProductionState : PanSemState (RiscV.Word 64) Unit :=
  { loadHitProductionState with memaddrs := fun _ => False }

private theorem loadHitDom (address : RiscV.Word 64) :
    loadHitProductionState.memaddrs address = (loadHitState 0).memaddrs address := by
  simp

private theorem loadMissDom (address : RiscV.Word 64) :
    loadMissProductionState.memaddrs address = loadMissState.memaddrs address := by
  simp

/-! ## Concrete flat-load recursion bridge to exact `mem_load` -/

private def recursiveLoadStructs : StructContext :=
  [("S", { fields := [("f", Shape.one)], size := 3 })]

private def recursiveLoadMemory : BitVec 64 → Option (PanValue (BitVec 64)) := fun address =>
  if address = 0 then some (.word (BitVec.ofNat 64 0x11))
  else if address = 8 then some (.word (BitVec.ofNat 64 0x22)) else none

private def recursiveLoadExactState : PanSemStateFiniteExact 64 Unit :=
  { loadHitState 0x11 with
    memory := fun address => if address = 0 then .word (BitVec.ofNat 64 0x11)
      else if address = 8 then .word (BitVec.ofNat 64 0x22) else .word 0
    memaddrs := fun address => address = 0 ∨ address = 8 }

private instance : DecidablePred recursiveLoadExactState.memaddrs := fun address => by
  change Decidable (address = 0 ∨ address = 8)
  infer_instance

private def recursiveLoadProductionState : PanSemState (RiscV.Word 64) Unit :=
  { loadHitProductionState with memaddrs := fun address => address = 0 || address = 8 }

private theorem recursiveLoadMemoryCodec :
    PanValueMemoryCodecRel recursiveLoadMemory recursiveLoadExactState := by
  intro address
  by_cases h0 : address = 0
  · subst address
    simp [recursiveLoadMemory, recursiveLoadExactState]
  · by_cases h8 : address = 8
    · subst address
      simp [recursiveLoadMemory, recursiveLoadExactState]
    · change (if address = 0 then some (PanValue.word (BitVec.ofNat 64 0x11))
          else if address = 8 then some (PanValue.word (BitVec.ofNat 64 0x22)) else none) = _
      rw [if_neg h0, if_neg h8]
      have hdomain : ¬ recursiveLoadExactState.memaddrs address := by
        change ¬ (address = 0 ∨ address = 8)
        exact not_or.mpr ⟨h0, h8⟩
      rw [if_neg hdomain]

private theorem recursiveLoadDomain (address : BitVec 64) :
    recursiveLoadProductionState.memaddrs address =
      decide (recursiveLoadExactState.memaddrs address) := by
  simp [recursiveLoadProductionState, recursiveLoadExactState]

private theorem recursiveLoadCtxBR : CtxBR recursiveLoadStructs := by
  intro p hp
  rcases p with ⟨name, info⟩
  simp [recursiveLoadStructs] at hp
  rcases hp with ⟨rfl, rfl⟩
  simp [NameRanged, ListParamByteRanged, ParamByteRanged, ShapeByteRanged]

/-- Concrete flat list recursion reads the second word at address 8 and agrees
    with the exact `mem_loads` result under the finite memory codec. -/
example :
    ((panValueFlatLoadListFuel recursiveLoadStructs
        (panValueFlatMachineReadWord recursiveLoadProductionState recursiveLoadMemory)
        panSemBitVec64BytesInWord
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatShapeFuel.panValueFlatShapeListFuel [.one, .one])
        [.one, .one] 0).map (List.map panValueToHOL) : Option (List (ValueHOL 64))) =
      some [.val (.word (BitVec.ofNat 64 0x11)), .val (.word (BitVec.ofNat 64 0x22))] := by
  calc
    _ = memLoadsHOLExact [ShapeHOL.one, ShapeHOL.one] 0
        recursiveLoadExactState.memaddrs recursiveLoadExactState.memory
        (structContextToHOL recursiveLoadStructs.toHOL) := by
      simpa [shapeToHOL] using panValueFlatLoadListFuel_memLoadsHOLExact recursiveLoadProductionState
        recursiveLoadExactState recursiveLoadStructs recursiveLoadMemory [.one, .one] 0
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatShapeFuel.panValueFlatShapeListFuel [.one, .one])
        recursiveLoadMemoryCodec recursiveLoadDomain recursiveLoadCtxBR
        (by
          intro shape hshape
          rcases List.mem_cons.mp hshape with hshape | hshape
          · cases hshape; simp [ShapeByteRanged]
          · rcases List.mem_cons.mp hshape with hshape | hshape
            · cases hshape; simp [ShapeByteRanged]
            · simp at hshape) (Nat.le_refl _)
    _ = some [.val (.word (BitVec.ofNat 64 0x11)), .val (.word (BitVec.ofNat 64 0x22))] := by
      simp [memLoadsHOLExact, memLoadHOLExact, recursiveLoadExactState,
        bytesInWordHOL, recursiveLoadStructs, structContextToHOL, StructContext.toHOL]

/-- The same recursive list is also assembled by the production `.comb` shape
    into the exact HOL `RStruct` result. -/
example :
    (panValueFlatLoadFuel recursiveLoadStructs
        (panValueFlatMachineReadWord recursiveLoadProductionState recursiveLoadMemory)
        panSemBitVec64BytesInWord
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatShapeFuel (.comb [.one, .one]))
        (.comb [.one, .one]) 0).map panValueToHOL =
      some (.rStruct
        [.val (.word (BitVec.ofNat 64 0x11)), .val (.word (BitVec.ofNat 64 0x22))]) := by
  calc
    _ = memLoadHOLExact (shapeToHOL (.comb [.one, .one])) 0
        recursiveLoadExactState.memaddrs recursiveLoadExactState.memory
        (structContextToHOL recursiveLoadStructs.toHOL) :=
      panValueFlatLoadFuel_memLoadHOLExact recursiveLoadProductionState
        recursiveLoadExactState recursiveLoadStructs recursiveLoadMemory
        (.comb [.one, .one]) 0
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatShapeFuel (.comb [.one, .one]))
        recursiveLoadMemoryCodec recursiveLoadDomain recursiveLoadCtxBR
        (by simp [ShapeByteRanged]) (Nat.le_refl _)
    _ = some (.rStruct
        [.val (.word (BitVec.ofNat 64 0x11)), .val (.word (BitVec.ofNat 64 0x22))]) := by
      simp [shapeToHOL, memLoadHOLExact, memLoadsHOLExact, bytesInWordHOL,
        recursiveLoadExactState, recursiveLoadStructs, structContextToHOL,
        StructContext.toHOL]

/-- Concrete named shape follows its context entry and the one-field recursion
    while encoding both structure and field names into `MlString`. -/
example :
    (panValueFlatLoadFuel recursiveLoadStructs
        (panValueFlatMachineReadWord recursiveLoadProductionState recursiveLoadMemory)
        panSemBitVec64BytesInWord
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatShapeFuel (.named "S"))
        (.named "S") 0).map panValueToHOL =
      some (.nStruct (Flapjack.Basis.Pure.MlString.ofString "S")
        [(Flapjack.Basis.Pure.MlString.ofString "f",
          .val (.word (BitVec.ofNat 64 0x11)))]) := by
  calc
    _ = memLoadHOLExact (shapeToHOL (.named "S")) 0 recursiveLoadExactState.memaddrs
        recursiveLoadExactState.memory (structContextToHOL recursiveLoadStructs.toHOL) :=
      panValueFlatLoadFuel_memLoadHOLExact recursiveLoadProductionState
        recursiveLoadExactState recursiveLoadStructs recursiveLoadMemory (.named "S") 0
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatShapeFuel (.named "S"))
        recursiveLoadMemoryCodec recursiveLoadDomain recursiveLoadCtxBR
        (by simp [ShapeByteRanged]) (Nat.le_refl _)
    _ = some (.nStruct (Flapjack.Basis.Pure.MlString.ofString "S")
        [(Flapjack.Basis.Pure.MlString.ofString "f",
          .val (.word (BitVec.ofNat 64 0x11)))]) := by
      simp [memLoadHOLExact, memLoadFldsHOLExact, paramToHOL,
        recursiveLoadExactState, recursiveLoadStructs, bytesInWordHOL,
        shapeToHOL, structContextToHOL, StructContext.toHOL, structInfoToHOL,
        sizeOfShapeWithContextHOL]

/-- The field-list subrecursion is also available directly, including its
    byte-name codec and the same eight-byte word stride. -/
example :
    ((panValueFlatLoadFieldsFuel recursiveLoadStructs
        (panValueFlatMachineReadWord recursiveLoadProductionState recursiveLoadMemory)
        panSemBitVec64BytesInWord
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatFieldsFuel [("f", Shape.one)])
        [("f", Shape.one)] 0).map (List.map (fun p =>
          (Flapjack.Basis.Pure.MlString.ofString p.1, panValueToHOL p.2))) :
          Option (List (MlS × ValueHOL 64))) =
      some [(Flapjack.Basis.Pure.MlString.ofString "f",
        .val (.word (BitVec.ofNat 64 0x11)))] := by
  calc
    _ = memLoadFldsHOLExact ([(Flapjack.Basis.Pure.MlString.ofString "f",
          ShapeHOL.one)]) 0 recursiveLoadExactState.memaddrs recursiveLoadExactState.memory
        (structContextToHOL recursiveLoadStructs.toHOL) := by
      simpa [paramToHOL, shapeToHOL] using panValueFlatLoadFieldsFuel_memLoadFldsHOLExact
        recursiveLoadProductionState recursiveLoadExactState recursiveLoadStructs recursiveLoadMemory
        [("f", Shape.one)] 0
        (panValueFlatContextFuel recursiveLoadStructs +
          panValueFlatFieldsFuel [("f", Shape.one)]) recursiveLoadMemoryCodec recursiveLoadDomain
        recursiveLoadCtxBR
        (by simp [ListParamByteRanged, ParamByteRanged, NameRanged, ShapeByteRanged])
        (Nat.le_refl _)
    _ = some [(Flapjack.Basis.Pure.MlString.ofString "f",
        .val (.word (BitVec.ofNat 64 0x11)))] := by
      simp [memLoadFldsHOLExact, memLoadHOLExact, recursiveLoadExactState,
        bytesInWordHOL]

private theorem addressConstExecCorrespondence {σ : Type} (state : PanSemStateFiniteExact 64 Unit)
    [DecidablePred state.memaddrs] (productionState : PanSemState (RiscV.Word 64) σ)
    (memory : BitVec 64 → Option (PanValue (BitVec 64)))
    (baseAddress topAddress : BitVec 64) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals memory baseAddress topAddress
        panSemBitVec64BytesInWord addressConst
        (memoryAccess := some (panSemBitVec64MemoryAccess productionState)))
      (state.evalHOLFinite (expToHOL addressConst)) := by
  simp only [PanSemDeclarationValueOptionRel, evalPanValueExp, expToHOL,
    PanSemStateFiniteExact.evalHOLFinite_const, panValueCodecRel_word]

/-- **Concrete executed-access witness, success.**  The executed RV64
    `memoryAccess` path against the direct HOL EVAL row `word_load_hit`. -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals (hitMemory 0x1122334455667788)
        0 100 panSemBitVec64BytesInWord (.load .one addressConst)
        (memoryAccess := some (panSemBitVec64MemoryAccess loadHitProductionState)))
      ((loadHitState 0x1122334455667788).evalHOLFinite
        (.load .one (expToHOL addressConst))) :=
  evalPanValueExp_load_one_option_correspondence_executed loadHitProductionState
    (loadHitState 0x1122334455667788) [] noLocals noGlobals
    (hitMemory 0x1122334455667788) 0 100 addressConst
    (hitMemoryCodecRel 0x1122334455667788) loadHitDom
    (addressConstExecCorrespondence (loadHitState 0x1122334455667788)
      loadHitProductionState (hitMemory 0x1122334455667788) 0 100)

/-- **Concrete executed-access witness, domain miss.**  Direct HOL EVAL row
    `word_load_miss=NONE` on the executed RV64 `memoryAccess` path. -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals missMemory
        0 100 panSemBitVec64BytesInWord (.load .one addressConst)
        (memoryAccess := some (panSemBitVec64MemoryAccess loadMissProductionState)))
      (loadMissState.evalHOLFinite (.load .one (expToHOL addressConst))) :=
  evalPanValueExp_load_one_option_correspondence_executed loadMissProductionState
    loadMissState [] noLocals noGlobals missMemory 0 100 addressConst
    missMemoryCodecRel loadMissDom
    (addressConstExecCorrespondence loadMissState loadMissProductionState missMemory 0 100)

/-- **Concrete executed-access witness, `.load32`.** -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals (hitMemory 0x1122334455667788)
        0 100 panSemBitVec64BytesInWord (.load32 addressConst)
        (memoryAccess := some (panSemBitVec64MemoryAccess (loadHitProductionState))))
      ((loadHitState 0x1122334455667788).evalHOLFinite (.load32 (expToHOL addressConst))) :=
  evalPanValueExp_load32_option_correspondence_executed (loadHitProductionState)
    (loadHitState 0x1122334455667788) [] noLocals noGlobals (hitMemory 0x1122334455667788) 0 100 addressConst
    (hitMemoryCodecRel 0x1122334455667788) (loadHitDom) (by rfl)
    (addressConstExecCorrespondence (loadHitState 0x1122334455667788) (loadHitProductionState) (hitMemory 0x1122334455667788) 0 100)

/-- **Concrete executed-access witness, `.load32`.** -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals (missMemory)
        0 100 panSemBitVec64BytesInWord (.load32 addressConst)
        (memoryAccess := some (panSemBitVec64MemoryAccess (loadMissProductionState))))
      ((loadMissState).evalHOLFinite (.load32 (expToHOL addressConst))) :=
  evalPanValueExp_load32_option_correspondence_executed (loadMissProductionState)
    (loadMissState) [] noLocals noGlobals (missMemory) 0 100 addressConst
    (missMemoryCodecRel) (loadMissDom) (by rfl)
    (addressConstExecCorrespondence (loadMissState) (loadMissProductionState) (missMemory) 0 100)

/-- **Concrete executed-access witness, `.loadByte`.** -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals (hitMemory 0x1122334455667788)
        0 100 panSemBitVec64BytesInWord (.loadByte addressConst)
        (memoryAccess := some (panSemBitVec64MemoryAccess (loadHitProductionState))))
      ((loadHitState 0x1122334455667788).evalHOLFinite (.loadByte (expToHOL addressConst))) :=
  evalPanValueExp_loadByte_option_correspondence_executed (loadHitProductionState)
    (loadHitState 0x1122334455667788) [] noLocals noGlobals (hitMemory 0x1122334455667788) 0 100 addressConst
    (hitMemoryCodecRel 0x1122334455667788) (loadHitDom) (by rfl)
    (addressConstExecCorrespondence (loadHitState 0x1122334455667788) (loadHitProductionState) (hitMemory 0x1122334455667788) 0 100)

/-- **Concrete executed-access witness, `.loadByte`.** -/
example :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp [] noLocals noGlobals (missMemory)
        0 100 panSemBitVec64BytesInWord (.loadByte addressConst)
        (memoryAccess := some (panSemBitVec64MemoryAccess (loadMissProductionState))))
      ((loadMissState).evalHOLFinite (.loadByte (expToHOL addressConst))) :=
  evalPanValueExp_loadByte_option_correspondence_executed (loadMissProductionState)
    (loadMissState) [] noLocals noGlobals (missMemory) 0 100 addressConst
    (missMemoryCodecRel) (loadMissDom) (by rfl)
    (addressConstExecCorrespondence (loadMissState) (loadMissProductionState) (missMemory) 0 100)



/-! ## Concrete executed-path fixed-load guards vs direct HOL rows

The expected values below are the literal outputs recorded by direct HOL EVAL
in `scripts/hol-probes/pan_fixed_load_probe.out` (generated from
`pancake/semantics/panSemScript.sml:86-109`), using the probe's little-endian
64-bit word cell `0x0807060504030201` at byte address 8:

* `byte_hit=SOME 2w`, `byte_miss=NONE`, `byte_big_endian=SOME 7w`;
* `load32_hit=SOME 0x4030201w`, `load32_unaligned=NONE`,
  `load32_domain_miss=NONE`, `load32_big_endian=SOME 0x8070605w`.

The guards run the executed RV64 `memoryAccess` path
(`evalPanValueExp ... (memoryAccess := some (panSemBitVec64MemoryAccess ...))`)
against that same fixture and compare with the literal row outputs.  The bridge
theorems `evalPanValueExp_load32_option_correspondence_executed` /
`..._loadByte_option_correspondence_executed` additionally relate each run to
the tagged finite evaluator. -/

/-- The fixed-load probe cell: word `0x0807060504030201` at byte address 8. -/
private abbrev fixedLoadMemory : BitVec 64 → Option (PanValue (BitVec 64)) :=
  fun _ => some (.word 0x0807060504030201)

/-- Production state matching the probe: word cell at address 8, memory domain
    exactly `{domainAddress}`, chosen endianness. -/
private abbrev fixedLoadProductionState (bigEndian : Bool) (domainAddress : BitVec 64) :
    PanSemState (RiscV.Word 64) Unit :=
  { locals := noLocals
    globals := noGlobals
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => some (.word (BitVec.ofNat 64 0x0807060504030201))
    memaddrs := fun address => address = domainAddress
    sharedMemaddrs := fun _ => false
    clock := 5
    be := bigEndian
    ffi := ()
    baseAddress := 0
    topAddress := 100 }

private def execLoad32 (state : PanSemState (RiscV.Word 64) Unit) (address : BitVec 64) :
    Option (PanValue (BitVec 64)) :=
  evalPanValueExp [] noLocals noGlobals fixedLoadMemory 0 100 panSemBitVec64BytesInWord
    (.load32 (.const address)) (memoryAccess := some (panSemBitVec64MemoryAccess state))

private def execLoadByte (state : PanSemState (RiscV.Word 64) Unit) (address : BitVec 64) :
    Option (PanValue (BitVec 64)) :=
  evalPanValueExp [] noLocals noGlobals fixedLoadMemory 0 100 panSemBitVec64BytesInWord
    (.loadByte (.const address)) (memoryAccess := some (panSemBitVec64MemoryAccess state))

/-- `true` when the run yields `.word expected`. -/
private def isWordResult (result : Option (PanValue (BitVec 64))) (expected : BitVec 64) : Bool :=
  match result with
  | some (.word value) => value == expected
  | _ => false

/-- `true` when the run rejects (HOL `NONE`). -/
private def isNoneResult (result : Option (PanValue (BitVec 64))) : Bool :=
  result.isNone

-- HOL rows `byte_hit`, `byte_miss`, `byte_big_endian`.
#guard isWordResult (execLoadByte (fixedLoadProductionState false 8#64) 9#64) 2#64
#guard isNoneResult (execLoadByte (fixedLoadProductionState false 16#64) 9#64)
#guard isWordResult (execLoadByte (fixedLoadProductionState true 8#64) 9#64) 7#64

-- HOL rows `load32_hit`, `load32_unaligned`, `load32_domain_miss`,
-- `load32_big_endian`.
#guard isWordResult (execLoad32 (fixedLoadProductionState false 8#64) 8#64) 0x04030201#64
#guard isNoneResult (execLoad32 (fixedLoadProductionState false 8#64) 9#64)
#guard isNoneResult (execLoad32 (fixedLoadProductionState false 16#64) 8#64)
#guard isWordResult (execLoad32 (fixedLoadProductionState true 8#64) 8#64) 0x08070605#64


end Flapjack.Test.DeclBridgeParity
