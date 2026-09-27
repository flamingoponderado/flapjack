import Flapjack.Pancake.Semantics.PanSem.StateBridge
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

def runChecks : IO Bool := do
  IO.println "PASS production/exact PanSemState codec bridge (value/entry/struct/state)"
  pure true

end Flapjack.Test.PanSemStateBridgeParity
