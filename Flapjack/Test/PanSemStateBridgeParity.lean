import Flapjack.Pancake.Semantics.PanSem.StateBridge
import Flapjack.Pancake.Semantics.PanSem.TotalEvalBridge
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# Regression examples for the production/exact `PanSemState` bridge

Kernel-checked examples for `Flapjack/Pancake/Semantics/PanSem/StateBridge.lean`:
the value, code-entry and struct-context codecs and the forward/reverse state
relation codecs on concrete inputs.  Everything here is untagged infrastructure.
-/

namespace Flapjack.Test.PanSemStateBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

abbrev W := BitVec 64

/-- HOL source of the memory-domain oracle rows checked below. -/
def memoryDomainProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:86-155,373-386,583-589"

/-- Regeneration command for the memory-domain oracle. -/
def memoryDomainProbeCommand : String :=
  "HOL_PROBE_ONLY=pan_sem_mem_domain_probeScript.sml scripts/hol-probes/regenerate.sh"

#guard memoryDomainProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:86-155,373-386,583-589"
#guard memoryDomainProbeCommand ==
  "HOL_PROBE_ONLY=pan_sem_mem_domain_probeScript.sml scripts/hol-probes/regenerate.sh"

/-- Word projection of a `ValueHOL` for guard comparison. -/
def valueWord? : ValueHOL 64 → Option Nat
  | .val (.word word) => some word.toNat
  | _ => none

/-- A byte-ranged production record value. -/
def recordValue : PanValue W :=
  .nStruct "Point" [("x", .word 3), ("y", .rStruct [.word 4])]

/-- Encoding then decoding the byte-ranged record recovers it. -/
example : panValueOfHOL (panValueToHOL recordValue) = recordValue := by
  apply panValueOfHOL_panValueToHOL
  simp [PanValueByteRanged, recordValue, NameRanged]

/-- Encoding then decoding a word value recovers it. -/
example : panValueOfHOL (panValueToHOL (PanValue.word (7 : W))) = .word 7 := by
  apply panValueOfHOL_panValueToHOL
  simp [PanValueByteRanged]

/-- Exact-side value round trip. -/
example :
    panValueToHOL (panValueOfHOL (ValueHOL.val (HolWordLab.word (11 : W)))) =
      .val (.word 11) := by
  simp

#guard valueWord? (panValueToHOL (.word (7 : W))) == some 7
#guard (holWordLabBits (HolWordLab.word (9 : W))).toNat == 9

/-- A concrete exact struct context. -/
def exactContext : StructContextExact :=
  [(Flapjack.Basis.Pure.MlString.ofString "S", { fields := [], size := 1 })]

example : panStructContextToHOL (panStructContextOfHOL exactContext) = exactContext := by
  simp only [panStructContextToHOL_panStructContextOfHOL]

/-- A concrete code entry round trips on the byte-ranged subset. -/
example :
    panLangEntryOfHOL (panLangEntryToHOL
      (([("x", Shape.one)], (Prog.skip : Prog W), Shape.one) :
        List (VarName × Shape) × Prog W × Shape)) =
      ([("x", Shape.one)], Prog.skip, Shape.one) := by
  apply panLangEntryOfHOL_panLangEntryToHOL
  simp [PanLangEntryByteRanged, ListParamByteRanged, ParamByteRanged, NameRanged,
    ProgByteRanged, ShapeByteRanged]

/-- A concrete exact state over `Unit` with empty code. -/
def exactState : PanSemStateExact 64 Unit where
  locals := fun name => if name = Flapjack.Basis.Pure.MlString.ofString "x"
    then some (.val (.word 7)) else none
  globals := fun _ => none
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

/-- Every exact `code` lookup is `none`, so the empty list is a support. -/
theorem emptyCodeSupport :
    ∃ keys : List MlS, ∀ key, exactState.code key ≠ none → key ∈ keys :=
  ⟨[], fun _ hkey => absurd rfl hkey⟩

instance decidableExactMemaddrs : DecidablePred exactState.memaddrs :=
  fun _ => isFalse (by simp [exactState])

instance decidableExactShMemaddrs : DecidablePred exactState.shMemaddrs :=
  fun _ => isFalse (by simp [exactState])

/-- The reverse codec lands in the state relation on the concrete state. -/
example : PanSemStateRel (panSemStateOfExact exactState emptyCodeSupport) exactState :=
  panSemStateRel_ofExact exactState emptyCodeSupport

/-- The exact round trip holds on the concrete state. -/
example :
    panSemStateToExact (panSemStateOfExact exactState emptyCodeSupport)
      exactState.memory (panSemStateMemoryRel_ofExact exactState emptyCodeSupport) =
      exactState :=
  panSemStateToExact_ofExact exactState emptyCodeSupport

/-! ## Negative regression: the `ffi` conjunct is load-bearing

`PanSemStateRel` compares the FFI carrier by equality.  These examples build an
exact state that agrees with `exactState` on every field except the FFI event
log, and show that the relation then cannot hold, so the `exact.ffi =
production.ffi` conjunct actually constrains FFI effects. -/

/-- `exactState`, but with one FFI event appended to the event log. -/
def exactStateDiffFfi : PanSemStateExact 64 Unit :=
  { exactState with
    ffi := { exactState.ffi with
      ioEvents := [{ name := .extCall
                        (Flapjack.Basis.Pure.MlString.MlString.implode []),
                     configuration := [], bytes := [] }] } }

/-- The two FFI carriers differ (the event logs are `[event]` versus `[]`). -/
theorem exactStateDiffFfi_ffi_ne : exactStateDiffFfi.ffi ≠ exactState.ffi := by
  intro h
  have hio := congrArg HolFfiState.ioEvents h
  simp [exactStateDiffFfi, exactState] at hio

/-- The relation fails when the exact state's FFI field is changed while the
    production side keeps the original FFI carrier: the missing conjunct would
    not have detected this, so the added `ffi` equality is load-bearing. -/
theorem bridgeRel_ffi_negative :
    ¬ PanSemStateRel (panSemStateOfExact exactState emptyCodeSupport)
        exactStateDiffFfi := by
  intro hrel
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hffi, _, _⟩ := hrel
  exact exactStateDiffFfi_ffi_ne (by simpa [panSemStateOfExact] using hffi)

/-! ## Partial production memory: revised `PanSemMemoryRel` witnesses

The production memory is partial; these regressions build the relation from an
actual parser-backed-shaped state whose cells exist only on `memaddrs`, and
check the in-domain hit, out-of-domain miss, and store-then-load behavior
against the direct HOL rows `domain_load_hit`, `domain_load_miss_present`, and
`domain_store_then_load_hit` in
`scripts/hol-probes/pan_sem_mem_domain_probe.out`. -/

/-- A partial production memory populated only at address `0`; off-domain
    addresses are absent (`none`), as in a parser-backed initial state. -/
def partialMemory : W → Option (PanValue W) :=
  fun address => if address = 0 then some (.word (0x1122334455667788 : W)) else none

/-- The addressable domain of `partialMemory`. -/
def partialMemaddrs : W → Bool :=
  fun address => address == 0

/-- A concrete partial production state over `Unit` with memory populated only
    on `partialMemaddrs`. -/
def bridgeState : PanSemState W Unit where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := []
  exceptionShapes := fun _ => none
  memory := partialMemory
  memaddrs := partialMemaddrs
  sharedMemaddrs := fun _ => false
  clock := 0
  be := false
  ffi := ()
  baseAddress := 0
  topAddress := 0

/-- The revised relation is satisfiable from the actual partial production
    state: totalizing its word-valued domain with `panSemMemoryExactOf` gives
    the forward witness, with no requirement on the absent off-domain cells. -/
theorem bridgeMemoryRel :
    PanSemMemoryRel partialMemaddrs partialMemory
      (panSemMemoryExactOf partialMemory) := by
  apply panSemMemoryRel_of_partial
  intro address hmemaddr
  have hzero : address = 0 := by
    simpa [partialMemaddrs] using hmemaddr
  exact ⟨(0x1122334455667788 : W), by simp [partialMemory, hzero]⟩

/-- The totalized exact memory keeps the in-domain word cell. -/
example : panSemMemoryExactOf partialMemory 0 = .word (0x1122334455667788 : W) := by
  simp [panSemMemoryExactOf, partialMemory]

/-- Off-domain totalization reads the fixed zero default, which is never
    consulted because the evaluator gates on `memaddrs`. -/
example : panSemMemoryExactOf partialMemory 8 = .word 0 := by
  simp [panSemMemoryExactOf, partialMemory]

/-- Store/update preserves the relation, matching HOL `mem_store`'s in-domain
    replacement (with the exact memory updated at the same address). -/
example :
    PanSemMemoryRel partialMemaddrs
      (fun current => if current == 0 then some (.word (0x99 : W)) else partialMemory current)
      (fun current => if current = 0 then .word (0x99 : W)
        else panSemMemoryExactOf partialMemory current) :=
  panSemMemoryRel_update partialMemaddrs partialMemory
    (panSemMemoryExactOf partialMemory) bridgeMemoryRel 0 (0x99 : W)

private def isNoneResult {α : Type} (result : Option α) : Bool :=
  match result with
  | none => true
  | some _ => false

-- HOL `domain_load_hit`: an in-domain `Load One` reads the word cell.
#guard
  match evalPanSemStateExp bridgeState (.load .one (.const 0)) with
  | some (.word value) => value == (0x1122334455667788 : W)
  | _ => false

-- HOL `domain_load_miss_present`: an out-of-domain `Load One` misses even
-- though the production cell is still present; the domain alone gates.
#guard isNoneResult
  (evalPanSemStateExp { bridgeState with memaddrs := fun _ => false }
    (.load .one (.const 0)))

/-- Under the relation, an in-domain word read returns the total exact word
    (production mirror of HOL `domain_load_hit`). -/
example :
    (panSemBitVec64MemoryAccess bridgeState).readWord bridgeState.memaddrs
        bridgeState.memory 8 0 = some (0x1122334455667788 : W) := by
  simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel, bridgeState,
    partialMemaddrs, partialMemory]

/-- Under the relation, an off-domain word read misses even though the cell is
    present (production mirror of HOL `domain_load_miss_present`). -/
example :
    (panSemBitVec64MemoryAccess { bridgeState with memaddrs := fun _ => false }).readWord
        (fun _ => false) bridgeState.memory 8 0 = none := by
  simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel]

/-- The production word store at an in-domain address returns the updated
    memory. -/
example :
    (panSemBitVec64MemoryAccess bridgeState).storeWord bridgeState.memaddrs
        bridgeState.memory 8 0 (0x99 : W)
      = some (fun current =>
          if current == 0 then some (.word (0x99 : W)) else bridgeState.memory current) := by
  simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel, bridgeState,
    partialMemaddrs]

/-- HOL `domain_store_then_load_hit`: the subsequent in-domain load reads the
    stored word (`mem_stores` then `mem_load`). -/
example :
    (panSemBitVec64MemoryAccess bridgeState).readWord bridgeState.memaddrs
        (fun current =>
          if current == 0 then some (.word (0x99 : W)) else bridgeState.memory current) 8 0
      = some (0x99 : W) := by
  simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel, bridgeState,
    partialMemaddrs]

/-! ## Executed-carrier agreement regressions (`TotalEvalBridge.lean`)

Kernel-checked fixtures for the untagged production/exact agreement interface:
a concrete `PanSemStateRelExec` state pair, the result/option relations, the
`Skip`/`Break`/`Continue`/`Tick`/`Annot` agreement theorems applied to it, and
negative checks that the `ffi` and result-payload conjuncts are load-bearing. -/

/-- Production FFI state whose oracle finalises with `failed` (no returned
    case), so the persistent oracle relation is vacuous. -/
def bridgeProdOracle : FfiOracle Unit := fun _ _ _ _ => .final .failed

/-- Exact FFI state oracle with the matching final outcome. -/
def bridgeHolOracle : HolOracle Unit := fun _ _ _ _ => .final .failed

/-- Production FFI carrier of the fixture. -/
def bridgeProdFfi : FfiState Unit :=
  { oracle := bridgeProdOracle, state := (), ioEvents := [] }

/-- Exact FFI carrier of the fixture. -/
def bridgeHolFfi : HolFfiState Unit :=
  { oracle := bridgeHolOracle, ffiState := (), ioEvents := [] }

/-- The two FFI carriers are related. -/
theorem bridgeFfiStateRel : FfiStateRel bridgeProdFfi bridgeHolFfi := by
  refine ⟨rfl, trivial, ?_⟩
  intro _name _holName _hname _state _configuration _holConfiguration
    _bytes _holBytes _hconf _hbytes
  simp [bridgeProdFfi, bridgeHolFfi, bridgeProdOracle, bridgeHolOracle,
    OracleResultRel, OutcomeRel]

/-- Complete production RV64 source state with empty maps, no memory, clock 5. -/
def bridgeExecProdState : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := bridgeProdFfi
    baseAddress := 0
    topAddress := 100 }

/-- Exact finite-map counterpart with the same scalar fields and empty maps. -/
def bridgeExecExactState : PanSemStateFiniteExact 64 Unit :=
  { locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    structs := []
    code := HolFiniteMapExact.empty
    eshapes := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := bridgeHolFfi
    baseAddr := 0
    topAddr := 100 }

/-- The concrete fixture satisfies the executed-carrier state relation. -/
theorem bridgeStateRelExec :
    PanSemStateRelExec bridgeExecProdState bridgeExecExactState.toExact := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name _; rfl
  · intro name _; rfl
  · rfl
  · intro name _; rfl
  · intro name _; rfl
  · intro address hmem
    simp [bridgeExecProdState] at hmem
  · intro address
    simp [bridgeExecProdState, bridgeExecExactState]
  · intro address
    simp [bridgeExecProdState, bridgeExecExactState]
  · rfl
  · rfl
  · exact bridgeFfiStateRel
  · rfl
  · rfl

/-- Positive result correspondence: the encoded production word equals the exact
    word payload. -/
example :
    PanSemHOLResultRel (.returned (.word (7 : W)))
      (.returned (.val (.word (7 : W)))) := by
  simp [PanSemHOLResultRel, panValueToHOL_word]

/-- Negative result correspondence: mismatched word payloads are not related. -/
example :
    ¬ PanSemHOLResultRel (.returned (.word (7 : W)))
      (.returned (.val (.word (8 : W)))) := by
  simp [PanSemHOLResultRel]

/-- The `Skip` agreement holds on the concrete fixture: normal completion on
    both sides with the state relation preserved. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate (fun _ _ => none) (.skip : Prog (RiscV.Word 64))
          bridgeExecProdState).1
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.skip : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate (fun _ _ => none) (.skip : Prog (RiscV.Word 64))
          bridgeExecProdState).2
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.skip : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_skip_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec

/-- The `Break` agreement holds on the concrete fixture. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate (fun _ _ => none) (.break : Prog (RiscV.Word 64))
          bridgeExecProdState).1
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.break : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate (fun _ _ => none) (.break : Prog (RiscV.Word 64))
          bridgeExecProdState).2
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.break : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_break_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec

/-- The `Continue` agreement holds on the concrete fixture. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate (fun _ _ => none) (.continue : Prog (RiscV.Word 64))
          bridgeExecProdState).1
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.continue : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate (fun _ _ => none) (.continue : Prog (RiscV.Word 64))
          bridgeExecProdState).2
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.continue : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_continue_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec

/-- The `Tick` agreement holds on the concrete fixture (clock 5, so the
    decrement branch). -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate (fun _ _ => none) (.tick : Prog (RiscV.Word 64))
          bridgeExecProdState).1
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.tick : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate (fun _ _ => none) (.tick : Prog (RiscV.Word 64))
          bridgeExecProdState).2
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.tick : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_tick_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec

/-- The `Annot` agreement holds on the concrete fixture. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate (fun _ _ => none)
          (.annot "tag" "text" : Prog (RiscV.Word 64)) bridgeExecProdState).1
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.annot (Flapjack.Basis.Pure.MlString.ofString "tag")
            (Flapjack.Basis.Pure.MlString.ofString "text") : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate (fun _ _ => none)
          (.annot "tag" "text" : Prog (RiscV.Word 64)) bridgeExecProdState).2
        (PanSemStateFiniteExact.evaluateHOLFiniteState bridgeExecExactState
          (.annot (Flapjack.Basis.Pure.MlString.ofString "tag")
            (Flapjack.Basis.Pure.MlString.ofString "text") : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_annot_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec
    (Flapjack.Basis.Pure.MlString.ofString "tag")
    (Flapjack.Basis.Pure.MlString.ofString "text")

/-- The `Tick` timeout branch also agrees: clock zero clears the locals on both
    sides. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate (fun _ _ => none) (.tick : Prog (RiscV.Word 64))
          { bridgeExecProdState with clock := 0 }).1
        (PanSemStateFiniteExact.evaluateHOLFiniteState
          { bridgeExecExactState with clock := 0 } (.tick : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate (fun _ _ => none) (.tick : Prog (RiscV.Word 64))
          { bridgeExecProdState with clock := 0 }).2
        (PanSemStateFiniteExact.evaluateHOLFiniteState
          { bridgeExecExactState with clock := 0 } (.tick : ProgHOL 64)).2.toExact := by
  have hrel : PanSemStateRelExec
      { bridgeExecProdState with clock := 0 }
      ({ bridgeExecExactState with clock := 0 }).toExact := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro name _; rfl
    · intro name _; rfl
    · rfl
    · intro name _; rfl
    · intro name _; rfl
    · intro address hmem
      simp [bridgeExecProdState] at hmem
    · intro address
      simp [bridgeExecProdState, bridgeExecExactState]
    · intro address
      simp [bridgeExecProdState, bridgeExecExactState]
    · rfl
    · rfl
    · exact bridgeFfiStateRel
    · rfl
    · rfl
  exact panSemTotalEvaluate_tick_agree (fun _ _ => none) _ _ hrel

/-- Negative check: the `ffi` conjunct is load-bearing.  Appending an FFI event
    to the exact side breaks `FfiStateRel`, hence `PanSemStateRelExec`. -/
def bridgeExecExactStateDiffFfi : PanSemStateFiniteExact 64 Unit :=
  { bridgeExecExactState with
    ffi := { bridgeHolFfi with
      ioEvents := [{ name := HolFfiName.extCall
                        (Flapjack.Basis.Pure.MlString.MlString.implode []),
                     configuration := [], bytes := [] }] } }

/-- The relation fails when the exact FFI field carries an event the production
    side does not, so the `FfiStateRel` conjunct matters. -/
theorem bridgeStateRelExec_ffi_negative :
    ¬ PanSemStateRelExec bridgeExecProdState bridgeExecExactStateDiffFfi.toExact := by
  intro hrel
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hffi, _, _⟩ := hrel
  simpa [bridgeExecProdState, bridgeExecExactStateDiffFfi, bridgeExecExactState,
    bridgeProdFfi, FfiEventListRel] using hffi.2.1

/-! ## Expression-evaluation agreement infrastructure

Kernel-checked concrete guards for the production/exact expression agreement in
`Flapjack/Pancake/Semantics/PanSem/TotalEvalExpBridge.lean`. -/

/-- The word projection of the encoding of a production word value. -/
example : panValueWordProjection (PanValue.word (7 : W)) = some 7 := by
  simp

/-- For a structured value the projection is `none` on both the production value
    and the encoded exact value. -/
example : panValueWordProjection (PanValue.rStruct ([] : List (PanValue W))) = none ∧
    valueIsWord (panValueToHOL (PanValue.rStruct ([] : List (PanValue W)))) = false := by
  simp [panValueToHOL_rStruct, valueIsWord]

/-- The exact shape of an encoded named structure is the encoded shape. -/
example : shapeOfHOLExact (panValueToHOL (PanValue.nStruct "P" ([] : List (String × PanValue W)))) =
    ShapeHOL.named (Flapjack.Basis.Pure.MlString.ofString "P") := by
  simpa [panValueShape, shapeToHOL] using
    shapeOfHOLExact_panValueToHOL ([] : StructContext)
      (PanValue.nStruct "P" ([] : List (String × PanValue W)))

/-- `ofString` is injective on byte-ranged names. -/
example : Flapjack.Basis.Pure.MlString.ofString "S" =
    Flapjack.Basis.Pure.MlString.ofString "T" → ("S" : String) = "T" :=
  ofString_injective_of_ranged (by decide) (by decide)

/-! ## Structured-constructor bridge guards

Kernel-checked guards for the `nStruct`/`nField`/`load` carrier bridges in
`TotalEvalExpBridge.lean`: the `HolValue` codec, the cache-augmented
`struct_info` encoding, named-field lookup commutation, and the folded
`nStruct` field-shape check. -/

/-- The `HolValue` codec encodes a named structure with `ofString` names. -/
example : holValueToHOL (HolValue.nStruct "P" [(("x" : String), HolValue.val (PanWordLab.word (3 : W)))]) =
    ValueHOL.nStruct (Flapjack.Basis.Pure.MlString.ofString "P")
      [(Flapjack.Basis.Pure.MlString.ofString "x", ValueHOL.val (HolWordLab.word (3 : W)))] := by
  simp [holValueToHOL]

/-- The cache-augmented `struct_info` encoding maps field shapes with `shapeToHOL`. -/
example : (structInfoCacheToHOL { fields := [("x", Shape.one)], size := 1 } : StructInfoHOLExact).fields =
    [(Flapjack.Basis.Pure.MlString.ofString "x", ShapeHOL.one)] := by
  simp [structInfoCacheToHOL, shapeToHOL]

/-- Named-field lookup commutes with the value codec. -/
example : Option.map panValueToHOL
      (lookupPanValueField "y"
        [("x", PanValue.word (1 : W)), ("y", PanValue.word (2 : W))]) =
    lookupFieldHOL (Flapjack.Basis.Pure.MlString.ofString "y")
      [(Flapjack.Basis.Pure.MlString.ofString "x", ValueHOL.val (HolWordLab.word (1 : W))),
       (Flapjack.Basis.Pure.MlString.ofString "y", ValueHOL.val (HolWordLab.word (2 : W)))] := by
  simpa using lookupPanValueField_map "y"
    [("x", PanValue.word (1 : W)), ("y", PanValue.word (2 : W))]
    (by decide) (by decide)

/-- The folded `nStruct` check equals the encoded-shape check on matching names. -/
example : panValueFieldsExactHOL ([] : StructContext)
      [("x", Shape.one)]
      [("x", PanValue.word (4 : W))] = true := by
  simp [panValueFieldsExactHOL, panShapeMatches, panValueShape]

def runChecks : IO Bool := do
  IO.println "PASS production/exact PanSemState codec bridge (value/entry/struct/state)"
  pure true

end Flapjack.Test.PanSemStateBridgeParity