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
  simp [loadHitProductionState, loadHitState]

private theorem loadMissDom (address : RiscV.Word 64) :
    loadMissProductionState.memaddrs address = loadMissState.memaddrs address := by
  simp [loadMissProductionState, loadMissState, loadHitProductionState]

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

end Flapjack.Test.DeclBridgeParity
