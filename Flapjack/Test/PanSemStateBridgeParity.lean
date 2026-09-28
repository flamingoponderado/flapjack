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
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

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

/-! ## Assembled all-constructor agreement guards

Kernel-checked guards for the assembled `evalPanValueExp_agree` and
`evalPanValueExp_byteRanged` (`TotalEvalExpBridge.lean`) on the concrete
executed-carrier fixture. -/

/-- The empty-maps fixture satisfies the byte-ranged execution premise. -/
theorem bridgeExecProdState_ranged : PanSemStateRelExecRanged bridgeExecProdState := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value h; simp [bridgeExecProdState] at h
  · intro name value h; simp [bridgeExecProdState] at h
  · intro p hp; simp [bridgeExecProdState, StructContext.toHOL] at hp

/-- The fixture's `memaddrs` is everywhere false. -/
instance decidableBridgeExecExactMemaddrs : DecidablePred bridgeExecExactState.memaddrs :=
  fun _ => isFalse (by simp [bridgeExecExactState])

/-- The assembled agreement holds for a constant expression on the fixture. -/
example :
    Option.map panValueToHOL (evalPanSemStateExp bridgeExecProdState (.const (7 : W))) =
      bridgeExecExactState.evalHOLFinite (expToHOL (.const (7 : W))) :=
  evalPanSemStateExp_agree bridgeExecProdState bridgeExecExactState bridgeStateRelExec
    bridgeExecProdState_ranged (.const (7 : W)) trivial

/-- The assembled agreement holds for a structured expression through the
    explicit state-owned memory access. -/
example :
    Option.map panValueToHOL
        (evalPanValueExp bridgeExecProdState.structs bridgeExecProdState.locals
          bridgeExecProdState.globals bridgeExecProdState.memory
          bridgeExecProdState.baseAddress bridgeExecProdState.topAddress
          panSemBitVec64BytesInWord (.rStruct [.const (3 : W), .const (4 : W)])
          (memoryAccess := some (panSemBitVec64MemoryAccess bridgeExecProdState))) =
      bridgeExecExactState.evalHOLFinite
        (expToHOL (.rStruct [.const (3 : W), .const (4 : W)])) :=
  evalPanValueExp_agree bridgeExecProdState bridgeExecExactState bridgeStateRelExec
    bridgeExecProdState_ranged (.rStruct [.const (3 : W), .const (4 : W)])
    (by simp [ExpByteRanged, ListExpByteRanged])

/-- The rangedness companion holds on a ranged constant. -/
example : PanValueByteRanged (PanValue.word (7 : W)) :=
  evalPanValueExp_byteRanged bridgeExecProdState bridgeExecProdState_ranged
    (some (panSemBitVec64MemoryAccess bridgeExecProdState)) (.const (7 : W)) trivial
    (.word (7 : W)) (by simp [evalPanValueExp])

-- The executed path computes the constant.
#guard
  match evalPanSemStateExp bridgeExecProdState (.const (7 : W)) with
  | some (.word value) => value == (7 : W)
  | _ => false

/-! ## Rangedness preservation and the `PanSemStateRelExec`/rangedness boundary

Kernel-checked witnesses for the preservation lemmas and the boundary
characterization added to `TotalEvalExpBridge.lean` (bead
`flapjack-pxn.18.4.3.77.2.15.1`): a ranged local update preserves
`PanSemStateRelExecRanged`, while a state whose local holds a non-byte-ranged
value is related by `PanSemStateRelExec` but not `PanSemStateRelExecRanged`, so
the rangedness premise is not implied by the state relation and must be closed
separately for runtime FFI/global values. -/

/-- The fixture with a byte-ranged record assigned into local `"x"` stays ranged. -/
example : PanSemStateRelExecRanged
    { bridgeExecProdState with
      locals := updatePanValueMap bridgeExecProdState.locals "x" recordValue } :=
  bridgeExecProdState_ranged.updateLocals "x" recordValue (by
    simp [PanValueByteRanged, recordValue, NameRanged])

/-- The expression-driven local assignment class preserves rangedness on the
    fixture: `x := 7`.  The value's rangedness comes from
    `evalPanValueExp_byteRanged`, not from a separate assumption. -/
example : PanSemStateRelExecRanged
    { bridgeExecProdState with
      locals := updatePanValueMap bridgeExecProdState.locals "x" (.word (7 : W)) } :=
  PanSemStateRelExecRanged.evalLocalUpdate bridgeExecProdState
    bridgeExecProdState_ranged (.const (7 : W)) trivial "x" (.word (7 : W))
    (by simp [evalPanValueExp])

/-- The out-of-range production value of the boundary witness. -/
def witnessNonRangedValue : PanValue W := nonByteRangedValue

/-- Production state: the empty fixture with the out-of-range value in local `"x"`. -/
def witnessProd : PanSemState W (FfiState Unit) :=
  { bridgeExecProdState with
    locals := updatePanValueMap bridgeExecProdState.locals "x" witnessNonRangedValue }

/-- Exact counterpart: the encoding of the out-of-range value at local
    `ofString "x"`. -/
def witnessExact : PanSemStateExact 64 Unit :=
  { bridgeExecExactState.toExact with
    locals := fun key =>
      if key = Flapjack.Basis.Pure.MlString.ofString "x"
      then some (panValueToHOL witnessNonRangedValue)
      else bridgeExecExactState.toExact.locals key }

/-- `PanSemStateRelExec` is preserved by a ranged-key local update on both sides;
    the exact side is updated at the `ofString` image of the key.  This is the
    local helper needed to exhibit the boundary witness. -/
private theorem PanSemStateRelExec.updateLocalsAt {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact)
    (name : VarName) (hname : NameRanged name) (value : PanValue (RiscV.Word 64)) :
    PanSemStateRelExec
      { production with locals := updatePanValueMap production.locals name value }
      { exact with locals := fun key =>
          if key = Flapjack.Basis.Pure.MlString.ofString name
          then some (panValueToHOL value) else exact.locals key } := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨?_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro key hkey
  by_cases hk : key == name
  · have hkeq : key = name := beq_iff_eq.mp hk
    subst hkeq
    simp [updatePanValueMap]
  · have hne : key ≠ name := fun hh => hk (beq_iff_eq.mpr hh)
    have hofne : Flapjack.Basis.Pure.MlString.ofString key ≠
        Flapjack.Basis.Pure.MlString.ofString name :=
      fun hh => hne (ofString_injective_of_ranged hkey hname hh)
    simp only [updatePanValueMap, if_neg hk, if_neg hofne]
    exact hl key hkey

/-- The boundary witness is related by `PanSemStateRelExec`. -/
theorem witnessStateRelExec : PanSemStateRelExec witnessProd witnessExact := by
  simpa only [witnessProd, witnessExact] using
    PanSemStateRelExec.updateLocalsAt bridgeStateRelExec "x" (by decide)
      witnessNonRangedValue

/-- The boundary witness production state fails `PanSemStateRelExecRanged`: this
    is the gap the range premise closes.  A `PanSemStateRelExec`-related state can
    still carry a non-byte-ranged runtime value. -/
theorem witnessProd_not_ranged : ¬ PanSemStateRelExecRanged witnessProd := by
  apply not_ranged_of_local_nonRanged witnessProd "x" witnessNonRangedValue
  · simp [witnessProd, updatePanValueMap]
  · exact nonByteRangedValue_not_ranged

/-! ## Runtime FFI/primitive value-range boundary (bead
    `flapjack-pxn.18.4.3.77.2.15.2`)

Kernel-checked guards for the boundary results added to `TotalEvalExpBridge.lean`:
the production `ExtCall` constructor preserves `PanSemStateRelExecRanged`
unconditionally, the production `Primitive` constructor preserves it under the
runtime premise `PanPrimitiveHandlerByteRanged`, and the boundary is crossed by a
non-byte-ranged primitive result or a pre-existing non-byte-ranged global. -/

/-- A byte-ranged primitive handler returning a constant word. -/
def byteRangedPrimitive : PanPrimitiveHandler W :=
  fun _ _ => some (PanValue.word (7 : W))

/-- A struct value whose structure name and fields are byte-ranged. -/
def goodStructValue : PanValue W :=
  .nStruct "Good" [("ok", .word (0 : W))]

/-- A value with the same shape as `goodStructValue` but a non-byte-ranged field
    name, so it is not `PanValueByteRanged` yet assignment-valid against it. -/
def badFieldValue : PanValue W :=
  .nStruct "Good" [("\u20ac", .word (0 : W))]

/-- The out-of-range field value is not byte-ranged. -/
theorem badFieldValue_not_ranged : ¬ PanValueByteRanged badFieldValue := by
  intro h
  simp only [badFieldValue, PanValueByteRanged, NameRanged, String.toList] at h
  exact absurd (h.2 ("\u20ac", PanValue.word (0 : W)) (by simp)).1 (by decide)

/-- A primitive handler returning the out-of-range field value. -/
def nonRangedPrimitive : PanPrimitiveHandler W :=
  fun _ _ => some badFieldValue

/-- The production `ExtCall` clause preserves `PanSemStateRelExecRanged` on the
    fixture for arbitrary constant arguments. -/
example : PanSemStateRelExecRanged
    (panSemTotalExtCallClause bridgeExecProdState ""
      (.const (0 : W)) (.const (0 : W)) (.const (0 : W)) (.const (0 : W))).2 :=
  PanSemStateRelExecRanged.extCallClause bridgeExecProdState_ranged ""
    (.const (0 : W)) (.const (0 : W)) (.const (0 : W)) (.const (0 : W))

/-- The production `Primitive` clause preserves `PanSemStateRelExecRanged` under
    the byte-ranged handler premise. -/
example : PanSemStateRelExecRanged
    (panSemTotalPrimitiveClause bridgeExecProdState "x" .addCarry
      [.const (7 : W)] byteRangedPrimitive).2 :=
  PanSemStateRelExecRanged.primitiveClause bridgeExecProdState_ranged "x" .addCarry
    [.const (7 : W)] byteRangedPrimitive (by
      intro operator values value h
      simp only [byteRangedPrimitive, Option.some.injEq] at h
      subst h
      simp [PanValueByteRanged])

/-- Production state carrying a byte-ranged `"Good"` struct in local `"x"`, so a
    shape-matching non-byte-ranged assignment is accepted. -/
def primitiveBoundaryState : PanSemState W (FfiState Unit) :=
  { bridgeExecProdState with
    locals := fun name => if name = "x" then some goodStructValue else none }

/-- The boundary state is `PanSemStateRelExecRanged` before the primitive call. -/
theorem primitiveBoundaryState_ranged :
    PanSemStateRelExecRanged primitiveBoundaryState := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value h
    simp only [primitiveBoundaryState, bridgeExecProdState] at h
    split at h
    · rename_i hname
      rw [Option.some.injEq] at h
      subst h
      simp [goodStructValue, PanValueByteRanged, NameRanged]
    · exact absurd h (by simp)
  · intro name value h
    simp only [primitiveBoundaryState, bridgeExecProdState] at h
    exact absurd h (by simp)
  · simpa only [primitiveBoundaryState, bridgeExecProdState] using
      bridgeExecProdState_ranged.2.2

/-- The primitive boundary is crossed: the non-byte-ranged handler result is
    installed into `"x"` and the resulting state fails
    `PanSemStateRelExecRanged`. -/
theorem primitiveBoundary_crossed :
    ¬ PanSemStateRelExecRanged
        (panSemTotalPrimitiveClause primitiveBoundaryState "x" .addCarry
          [] nonRangedPrimitive).2 := by
  apply primitiveClause_not_ranged_of_nonRanged primitiveBoundaryState "x" .addCarry
    [] nonRangedPrimitive [] badFieldValue
  · simp [evalPanSemStateExps, evalPanValueExps, evalPanValueExp.evalPanValueExps]
  · rfl
  · simp [panValueAssignmentValid, primitiveBoundaryState, bridgeExecProdState,
      goodStructValue, badFieldValue, panValueShape, panShapeMatches]
  · exact badFieldValue_not_ranged

/-- A state carrying a non-byte-ranged value in global `"g"` (the initial/stored
    global boundary). -/
def badGlobalState : PanSemState W (FfiState Unit) :=
  { bridgeExecProdState with
    globals := fun name => if name = "g" then some badFieldValue else none }

/-- The `ExtCall` boundary is not repaired: it leaves the non-byte-ranged global
    unchanged, so the resulting state still fails `PanSemStateRelExecRanged`. -/
example : ¬ PanSemStateRelExecRanged
    (panSemTotalExtCallClause badGlobalState ""
      (.const (0 : W)) (.const (0 : W)) (.const (0 : W)) (.const (0 : W))).2 :=
  extCallClause_not_ranged_of_global_nonRanged badGlobalState ""
    (.const (0 : W)) (.const (0 : W)) (.const (0 : W)) (.const (0 : W))
    "g" badFieldValue (by simp [badGlobalState]) badFieldValue_not_ranged

/-! ## Local/global value-map and result-variable update preservation (bead
    `flapjack-pxn.18.4.3.77.2.13.1`)

Kernel-checked guards for the untagged preservation lemmas added to
`TotalEvalBridge.lean`: a production local/global `updatePanValueMap` write and a
`resVar` restore are paired with the exact `setVarHOLFinite`/`setGlobalHOLFinite`
and `HolFiniteMapExact.resVarEq` updates, with the lookup at the written key
receiving the related value and other keys unchanged. -/

/-- The local already exists on the exact fixture, so the assignment-validity
    case is realizable. -/
def bridgeAssignExactState : PanSemStateFiniteExact 64 Unit :=
  { bridgeExecExactState with
    locals := (HolFiniteMapExact.empty.update
      (Flapjack.Basis.Pure.MlString.ofString "x", panValueToHOL (.word (7 : W)))) }

/-- Production fixture whose local `"x"` holds the word `7`. -/
def bridgeAssignProdState : PanSemState W (FfiState Unit) :=
  { bridgeExecProdState with
    locals := updatePanValueMap bridgeExecProdState.locals "x" (.word (7 : W)) }

/-- The assignment fixture satisfies the executed-carrier relation. -/
theorem bridgeAssignStateRelExec :
    PanSemStateRelExec bridgeAssignProdState bridgeAssignExactState.toExact :=
  PanSemStateRelExec.updateLocals bridgeStateRelExec "x" (by decide) (.word (7 : W))

/-- Pointwise local agreement at the written key: the exact lookup is the encoded
    written value. -/
example :
    Option.map panValueToHOL
        (updatePanValueMap bridgeExecProdState.locals "x" recordValue "x") =
      (bridgeExecExactState.locals.update
        (Flapjack.Basis.Pure.MlString.ofString "x",
          panValueToHOL recordValue)).lookup
        (Flapjack.Basis.Pure.MlString.ofString "x") :=
  updatePanValueMap_agree bridgeExecProdState.locals bridgeExecExactState.locals
    bridgeStateRelExec.1 "x" (by decide) recordValue "x" (by decide)

/-- Pointwise local agreement at an unrelated key keeps the old related value. -/
example :
    Option.map panValueToHOL
        (updatePanValueMap bridgeExecProdState.locals "x" recordValue "y") =
      (bridgeExecExactState.locals.update
        (Flapjack.Basis.Pure.MlString.ofString "x",
          panValueToHOL recordValue)).lookup
        (Flapjack.Basis.Pure.MlString.ofString "y") :=
  updatePanValueMap_agree bridgeExecProdState.locals bridgeExecExactState.locals
    bridgeStateRelExec.1 "x" (by decide) recordValue "y" (by decide)

/-- A local assignment preserves the executed-carrier relation on the fixture. -/
example : PanSemStateRelExec
    { bridgeExecProdState with
      locals := updatePanValueMap bridgeExecProdState.locals "x" recordValue }
    (setVarHOLFinite (Flapjack.Basis.Pure.MlString.ofString "x")
      (panValueToHOL recordValue) bridgeExecExactState).toExact :=
  PanSemStateRelExec.updateLocals bridgeStateRelExec "x" (by decide) recordValue

/-- A global assignment preserves the executed-carrier relation on the fixture. -/
example : PanSemStateRelExec
    { bridgeExecProdState with
      globals := updatePanValueMap bridgeExecProdState.globals "g" recordValue }
    (setGlobalHOLFinite (Flapjack.Basis.Pure.MlString.ofString "g")
      (panValueToHOL recordValue) bridgeExecExactState).toExact :=
  PanSemStateRelExec.updateGlobals bridgeStateRelExec "g" (by decide) recordValue

/-- A `resVar` overwrite restore preserves the relation (the `some` branch). -/
example : PanSemStateRelExec
    { bridgeExecProdState with
      locals := resVar bridgeExecProdState.locals ("x", some recordValue) }
    ({ bridgeExecExactState with
       locals := HolFiniteMapExact.resVarEq bridgeExecExactState.locals
         (Flapjack.Basis.Pure.MlString.ofString "x",
           some (panValueToHOL recordValue)) }).toExact :=
  PanSemStateRelExec.resVarLocals bridgeStateRelExec "x" (by decide) (some recordValue)

/-- A `resVar` delete restore preserves the relation (the `none` branch). -/
example : PanSemStateRelExec
    { bridgeExecProdState with
      locals := resVar bridgeExecProdState.locals ("x", none) }
    ({ bridgeExecExactState with
       locals := HolFiniteMapExact.resVarEq bridgeExecExactState.locals
         (Flapjack.Basis.Pure.MlString.ofString "x", none) }).toExact :=
  PanSemStateRelExec.resVarLocals bridgeStateRelExec "x" (by decide) none

/-- The assignment fixture is byte-ranged (it stores only the word `7`). -/
theorem bridgeAssignProdState_ranged :
    PanSemStateRelExecRanged bridgeAssignProdState := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value h
    simp only [bridgeAssignProdState, bridgeExecProdState, updatePanValueMap] at h
    split at h
    · rename_i hname
      rw [Option.some.injEq] at h
      subst h
      simp [PanValueByteRanged]
    · exact absurd h (by simp)
  · intro name value h
    simp only [bridgeAssignProdState, bridgeExecProdState] at h
    exact absurd h (by simp)
  · simpa only [bridgeAssignProdState, bridgeExecProdState] using
      bridgeExecProdState_ranged.2.2

instance decidableBridgeAssignExactMemaddrs : DecidablePred bridgeAssignExactState.memaddrs :=
  fun _ => isFalse (by simp [bridgeAssignExactState, bridgeExecExactState])

/-- The fully-assembled `Assign` constructor agreement (production value
    evaluation, validity parity, local update preservation) holds on the
    fixture for `x := 7`. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none) (.assign .local "x" (.const (7 : W)))
        bridgeAssignProdState).1
      (evaluateHOLFiniteState bridgeAssignExactState
        (.assign .local (Flapjack.Basis.Pure.MlString.ofString "x")
          (expToHOL (.const (7 : W))))).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none) (.assign .local "x" (.const (7 : W)))
        bridgeAssignProdState).2
      (evaluateHOLFiniteState bridgeAssignExactState
        (.assign .local (Flapjack.Basis.Pure.MlString.ofString "x")
          (expToHOL (.const (7 : W))))).2.toExact :=
  panSemTotalEvaluate_assign_agree (fun _ _ => none) bridgeAssignProdState
    bridgeAssignExactState bridgeAssignStateRelExec bridgeAssignProdState_ranged
    .local "x" (by decide) (.const (7 : W)) trivial

/-! ## Program rangedness projects to the bridge expression premise (bead
    `flapjack-pxn.18.4.3.77.2.15`)

`expsOf_byteRanged` (`Flapjack/Pancake/PanLang/Prog.lean`) turns the executed
`ProgByteRanged` program hypothesis into the `ExpByteRanged` premise of the
expression bridge, and `panSemTotalEvaluate_assign_agree_of_progByteRanged`
discharges the `NameRanged`/`ExpByteRanged` premises of the assembled `Assign`
slice.  The fixtures below are kernel-checked guards for both. -/

/-- A byte-ranged single-assignment program. -/
def bridgeAssignProgram : Prog W := .assign .local "x" (.const (7 : W))

/-- The fixture program is `ProgByteRanged`. -/
theorem bridgeAssignProgram_byteRanged : ProgByteRanged bridgeAssignProgram := by
  simp [bridgeAssignProgram, ProgByteRanged, ExpByteRanged, NameRanged]

/-- Its evaluated expression is byte-ranged by projection from the program. -/
example : ExpByteRanged (.const (7 : W)) :=
  expsOf_byteRanged bridgeAssignProgram bridgeAssignProgram_byteRanged
    (.const (7 : W)) (by simp [bridgeAssignProgram, expsOf])

/-- The agreement with the expression premise discharged from `ProgByteRanged`. -/
example :
    Option.map panValueToHOL (evalPanSemStateExp bridgeExecProdState (.const (7 : W))) =
      bridgeExecExactState.evalHOLFinite (expToHOL (.const (7 : W))) :=
  evalPanSemStateExp_agree_of_mem_expsOf bridgeExecProdState bridgeExecExactState
    bridgeStateRelExec bridgeExecProdState_ranged bridgeAssignProgram
    bridgeAssignProgram_byteRanged (.const (7 : W))
    (by simp [bridgeAssignProgram, expsOf])

/-- The assembled `Assign` slice with both expression premises discharged from
    the production program node's `ProgByteRanged` hypothesis. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none) bridgeAssignProgram bridgeAssignProdState).1
      (evaluateHOLFiniteState bridgeAssignExactState
        (.assign .local (Flapjack.Basis.Pure.MlString.ofString "x")
          (expToHOL (.const (7 : W))))).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none) bridgeAssignProgram bridgeAssignProdState).2
      (evaluateHOLFiniteState bridgeAssignExactState
        (.assign .local (Flapjack.Basis.Pure.MlString.ofString "x")
          (expToHOL (.const (7 : W))))).2.toExact :=
  panSemTotalEvaluate_assign_agree_of_progByteRanged (fun _ _ => none)
    bridgeAssignProdState bridgeAssignExactState bridgeAssignStateRelExec
    bridgeAssignProdState_ranged .local "x" (.const (7 : W))
    bridgeAssignProgram_byteRanged

/-! ## Production/exact `Return`/`Raise` agreement guards (bead
    `flapjack-pxn.18.4.3.77.2.14.1`)

Kernel-checked examples for `panSemTotalEvaluate_return_agree` and
`panSemTotalEvaluate_raise_agree` on concrete related state pairs, covering the
expression-failure, oversized-value, absent-exception-shape and
mismatched-exception-shape branches. -/

/-- A production context whose `"Big"` struct has 100 words, so its `named`
    shape exceeds the `≤ 32` size bound. -/
def bridgeBigStructProdState : PanSemState W (FfiState Unit) :=
  { bridgeExecProdState with
    structs := [("Big", { fields := [], size := 100 })] }

/-- The exact counterpart of `bridgeBigStructProdState`. -/
def bridgeBigStructExactState : PanSemStateFiniteExact 64 Unit :=
  { bridgeExecExactState with
    structs := panStructContextToHOL [("Big", { fields := [], size := 100 })] }

/-- The oversized-shape fixture satisfies the executed-carrier relation. -/
theorem bridgeBigStructStateRelExec :
    PanSemStateRelExec bridgeBigStructProdState bridgeBigStructExactState.toExact := by
  obtain ⟨hl, hg, _, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := bridgeStateRelExec
  exact ⟨hl, hg, rfl, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩

/-- The oversized-shape fixture is byte-ranged. -/
theorem bridgeBigStructStateRanged :
    PanSemStateRelExecRanged bridgeBigStructProdState := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value h; simp [bridgeBigStructProdState, bridgeExecProdState] at h
  · intro name value h; simp [bridgeBigStructProdState, bridgeExecProdState] at h
  · intro p hp
    simp only [bridgeBigStructProdState, StructContext.toHOL, List.map_cons,
      List.map_nil] at hp
    obtain rfl := List.mem_singleton.mp hp
    simp [NameRanged, StructInfoByteRanged, ListParamByteRanged]

instance decidableBridgeBigStructExactMemaddrs :
    DecidablePred bridgeBigStructExactState.memaddrs :=
  fun _ => isFalse (by simp [bridgeBigStructExactState, bridgeExecExactState])

/-- `Return` success: a byte-ranged word within the size bound. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.return (expOfHOL (.const (7 : W))) : Prog W) bridgeExecProdState).1
      (evaluateHOLFiniteState bridgeExecExactState
        (.return (.const (7 : W)) : ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.return (expOfHOL (.const (7 : W))) : Prog W) bridgeExecProdState).2
      (evaluateHOLFiniteState bridgeExecExactState
        (.return (.const (7 : W)) : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_return_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec bridgeExecProdState_ranged (.const (7 : W))

/-- `Return` expression failure: the source evaluates to `none`. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.return (expOfHOL (.var .local
          (Flapjack.Basis.Pure.MlString.ofString "missing"))) : Prog W)
        bridgeExecProdState).1
      (evaluateHOLFiniteState bridgeExecExactState
        (.return (.var .local (Flapjack.Basis.Pure.MlString.ofString "missing")) :
          ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.return (expOfHOL (.var .local
          (Flapjack.Basis.Pure.MlString.ofString "missing"))) : Prog W)
        bridgeExecProdState).2
      (evaluateHOLFiniteState bridgeExecExactState
        (.return (.var .local (Flapjack.Basis.Pure.MlString.ofString "missing")) :
          ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_return_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec bridgeExecProdState_ranged
    (.var .local (Flapjack.Basis.Pure.MlString.ofString "missing"))

/-- `Return` size failure: the value shape exceeds 32 words. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.return (expOfHOL (.nstruct (Flapjack.Basis.Pure.MlString.ofString "Big") [])) :
          Prog W) bridgeBigStructProdState).1
      (evaluateHOLFiniteState bridgeBigStructExactState
        (.return (.nstruct (Flapjack.Basis.Pure.MlString.ofString "Big") []) :
          ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.return (expOfHOL (.nstruct (Flapjack.Basis.Pure.MlString.ofString "Big") [])) :
          Prog W) bridgeBigStructProdState).2
      (evaluateHOLFiniteState bridgeBigStructExactState
        (.return (.nstruct (Flapjack.Basis.Pure.MlString.ofString "Big") []) :
          ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_return_agree (fun _ _ => none) bridgeBigStructProdState
    bridgeBigStructExactState bridgeBigStructStateRelExec bridgeBigStructStateRanged
    (.nstruct (Flapjack.Basis.Pure.MlString.ofString "Big") [])

/-- Production fixture with the declared exception shape `"E" ↦ one`. -/
def bridgeRaiseProdState : PanSemState W (FfiState Unit) :=
  { bridgeExecProdState with
    exceptionShapes := fun name => if name == "E" then some Shape.one else none }

/-- Exact counterpart of `bridgeRaiseProdState`. -/
def bridgeRaiseExactState : PanSemStateFiniteExact 64 Unit :=
  { bridgeExecExactState with
    eshapes := HolFiniteMapExact.empty.update
      (Flapjack.Basis.Pure.MlString.ofString "E", ShapeHOL.one) }

/-- The exception-shape fixture satisfies the executed-carrier relation. -/
theorem bridgeRaiseStateRelExec :
    PanSemStateRelExec bridgeRaiseProdState bridgeRaiseExactState.toExact := by
  obtain ⟨hl, hg, hs, hc, _, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := bridgeStateRelExec
  refine ⟨hl, hg, hs, hc, ?_, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro name hname
  by_cases hE : (name == "E") = true
  · have hnameEq : name = "E" := beq_iff_eq.mp hE
    subst hnameEq
    simp [bridgeRaiseProdState, bridgeRaiseExactState,
      HolFiniteMapExact.lookup_update, FUPDATE, shapeToHOL]
  · have hof : (Flapjack.Basis.Pure.MlString.ofString "E" ==
        Flapjack.Basis.Pure.MlString.ofString name) = false := by
      rw [beq_eq_false_iff_ne]
      intro hh
      exact hE (beq_iff_eq.mpr (ofString_injective_of_ranged
        (by decide : NameRanged "E") hname hh).symm)
    have hne : ¬ name = "E" := fun h => hE (beq_iff_eq.mpr h)
    simp [bridgeRaiseProdState, bridgeRaiseExactState,
      HolFiniteMapExact.lookup_update, FUPDATE, hof, hne]

/-- The exception fixture is byte-ranged. -/
theorem bridgeRaiseProdState_ranged : PanSemStateRelExecRanged bridgeRaiseProdState := by
  obtain ⟨hl, hg, hs⟩ := bridgeExecProdState_ranged
  exact ⟨hl, hg, hs⟩

instance decidableBridgeRaiseExactMemaddrs :
    DecidablePred bridgeRaiseExactState.memaddrs :=
  fun _ => isFalse (by simp [bridgeRaiseExactState, bridgeExecExactState])

/-- The declared exception shape of the fixture is byte-ranged. -/
theorem bridgeRaiseProdState_eshapesRanged :
    ∀ eid shape, bridgeRaiseProdState.exceptionShapes eid = some shape →
      ShapeByteRanged shape := by
  intro eid shape h
  simp only [bridgeRaiseProdState] at h
  split at h
  · rw [Option.some.injEq] at h
    subst h
    simp [ShapeByteRanged]
  · exact absurd h (by simp)

/-- The empty fixture has no declared exception shapes. -/
theorem bridgeExecProdState_eshapesRanged :
    ∀ eid shape, bridgeExecProdState.exceptionShapes eid = some shape →
      ShapeByteRanged shape := by
  intro eid shape h
  simp [bridgeExecProdState] at h

/-- `Raise` success: the declared `"E" ↦ one` shape matches the word value. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.const (7 : W))) : Prog W) bridgeRaiseProdState).1
      (evaluateHOLFiniteState bridgeRaiseExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W)) :
          ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.const (7 : W))) : Prog W) bridgeRaiseProdState).2
      (evaluateHOLFiniteState bridgeRaiseExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W)) :
          ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_raise_agree (fun _ _ => none) bridgeRaiseProdState
    bridgeRaiseExactState bridgeRaiseStateRelExec bridgeRaiseProdState_ranged
    bridgeRaiseProdState_eshapesRanged
    (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W))

/-- `Raise` shape mismatch: `one` does not match the `"X"` struct shape. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.nstruct (Flapjack.Basis.Pure.MlString.ofString "X") [])) :
          Prog W) bridgeRaiseProdState).1
      (evaluateHOLFiniteState bridgeRaiseExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E")
          (.nstruct (Flapjack.Basis.Pure.MlString.ofString "X") []) :
          ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.nstruct (Flapjack.Basis.Pure.MlString.ofString "X") [])) :
          Prog W) bridgeRaiseProdState).2
      (evaluateHOLFiniteState bridgeRaiseExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E")
          (.nstruct (Flapjack.Basis.Pure.MlString.ofString "X") []) :
          ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_raise_agree (fun _ _ => none) bridgeRaiseProdState
    bridgeRaiseExactState bridgeRaiseStateRelExec bridgeRaiseProdState_ranged
    bridgeRaiseProdState_eshapesRanged
    (Flapjack.Basis.Pure.MlString.ofString "E")
    (.nstruct (Flapjack.Basis.Pure.MlString.ofString "X") [])

/-- `Raise` absent shape: no declared shape for `"E"`. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.const (7 : W))) : Prog W) bridgeExecProdState).1
      (evaluateHOLFiniteState bridgeExecExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W)) :
          ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.const (7 : W))) : Prog W) bridgeExecProdState).2
      (evaluateHOLFiniteState bridgeExecExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W)) :
          ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_raise_agree (fun _ _ => none) bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec bridgeExecProdState_ranged
    bridgeExecProdState_eshapesRanged
    (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W))

/-- The `Raise` agreement no longer takes `hexnRanged` as a free premise: the
    exception-shape rangedness is intrinsic to the fixture state. -/
theorem bridgeRaiseProdState_exceptionShapesRanged :
    PanSemExceptionShapesRanged bridgeRaiseProdState :=
  bridgeRaiseProdState_eshapesRanged

/-- `panSemTotalEvaluate` preserves `PanSemExceptionShapesRanged`: it never
    writes `exceptionShapes`, so the `Raise` premise is intrinsic to reachable
    production execution. -/
example : PanSemExceptionShapesRanged
    (panSemTotalEvaluate (fun _ _ => none)
      (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
        (expOfHOL (.const (7 : W))) : Prog W) bridgeRaiseProdState).2 :=
  panSemTotalEvaluate_exceptionShapesRanged (fun _ _ => none)
    (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
      (expOfHOL (.const (7 : W))) : Prog W)
    bridgeRaiseProdState bridgeRaiseProdState_exceptionShapesRanged

/-- `Raise` agreement with `hexnRanged` discharged from the intrinsic
    `PanSemExceptionShapesRanged` predicate. -/
example : PanSemHOLResultOptionRel
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.const (7 : W))) : Prog W) bridgeRaiseProdState).1
      (evaluateHOLFiniteState bridgeRaiseExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W)) :
          ProgHOL 64)).1 ∧
    PanSemStateRelExec
      (panSemTotalEvaluate (fun _ _ => none)
        (.raise (toStringOfBytes (Flapjack.Basis.Pure.MlString.ofString "E"))
          (expOfHOL (.const (7 : W))) : Prog W) bridgeRaiseProdState).2
      (evaluateHOLFiniteState bridgeRaiseExactState
        (.raise (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W)) :
          ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_raise_agree_of_exceptionShapesRanged (fun _ _ => none)
    bridgeRaiseProdState bridgeRaiseExactState bridgeRaiseStateRelExec
    bridgeRaiseProdState_ranged bridgeRaiseProdState_exceptionShapesRanged
    (Flapjack.Basis.Pure.MlString.ofString "E") (.const (7 : W))

/-- A byte-ranged `exnDecl` list yields a ranged production exception map: the
    initial-state obligation for compiled declarations. -/
example : PanSemExceptionShapesRanged
    { bridgeExecProdState with
      exceptionShapes := fun name => panPropsALookupEq name
        (exceptionEntries [Decl.exnDecl (α := W) "E" Shape.one]) } :=
  panSemExceptionShapesRanged_of_exceptionEntries bridgeExecProdState
    [Decl.exnDecl (α := W) "E" Shape.one]
    (by
      intro declaration hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact ⟨by decide, by simp [ShapeByteRanged]⟩)

/-- Kernel-checked regression for the `ShMemLoad` production/exact agreement
    (`flapjack-pxn.18.4.3.77.2.14.12`) on the bridge fixture: the theorem is
    instantiated with a constant address expression, a local destination and a
    byte-ranged primitive handler. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate byteRangedPrimitive
          (.shMemLoad .opW .local (toStringOfBytes (ofString "x"))
            (expOfHOL (ExpHOL.const (0 : W))) : Prog W) bridgeExecProdState).1
        (evaluateHOLFiniteState bridgeExecExactState
          (.shMemLoad .opW .local (ofString "x")
            (ExpHOL.const (0 : W)) : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate byteRangedPrimitive
          (.shMemLoad .opW .local (toStringOfBytes (ofString "x"))
            (expOfHOL (ExpHOL.const (0 : W))) : Prog W) bridgeExecProdState).2
        (evaluateHOLFiniteState bridgeExecExactState
          (.shMemLoad .opW .local (ofString "x")
            (ExpHOL.const (0 : W)) : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_shMemLoad_agree byteRangedPrimitive bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec bridgeExecProdState_ranged .opW .local
    (ofString "x") (ExpHOL.const (0 : W))

/-- The canonical `panSemTotalEvaluateCake` entrypoint (the executable
    production `panSemTotalEvaluate` specialized to the canonical `panPrimopHOL`
    handler) exercises the proved Primitive-clause agreement on the
    executed-carrier fixture, so the `.77.2.14` assembly has an explicit
    reviewable use-site. -/
example :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluateCake
          (.primitive "x" .addCarry ([.const (7 : W)] : List (Exp W)))
          bridgeExecProdState).1
        (evaluateHOLFiniteState bridgeExecExactState
          (.primitive (ofString "x") .addCarry
            (([.const (7 : W)] : List (Exp W)).map expToHOL))).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluateCake
          (.primitive "x" .addCarry ([.const (7 : W)] : List (Exp W)))
          bridgeExecProdState).2
        (evaluateHOLFiniteState bridgeExecExactState
          (.primitive (ofString "x") .addCarry
            (([.const (7 : W)] : List (Exp W)).map expToHOL))).2.toExact :=
  panSemTotalEvaluateCake_primitive_agree_of_progByteRanged bridgeExecProdState
    bridgeExecExactState bridgeStateRelExec bridgeExecProdState_ranged "x" .addCarry
    ([.const (7 : W)] : List (Exp W))
    (by
      simp only [ProgByteRanged, NameRanged]
      exact ⟨by decide, fun e he => by
        simp only [List.mem_singleton] at he
        subst he
        trivial⟩)

def runChecks : IO Bool := do
  IO.println "PASS production/exact PanSemState codec bridge (value/entry/struct/state)"
  pure true

end Flapjack.Test.PanSemStateBridgeParity
