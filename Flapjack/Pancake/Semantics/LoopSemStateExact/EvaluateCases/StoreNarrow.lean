import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Store
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.FfiHook

/-! Native cross-carrier infrastructure for HOL Loop Store32/StoreByte clauses
(loopSemScript.sml:325-337), not ports of independent HOL declarations.
These 64-bit canonical hooks reuse the reviewed wordSem memory operations.
Full runtime hook-bundle selection and evaluator simulation remain open. -/
namespace Flapjack

/-- Replace production memory with the exact word-location image. -/
def loopMachineReplaceMemory {width : Nat} [NeZero width] {F : Type}
    (machine : LoopMachineState (BitVec width) F)
    (memory : BitVec width → WordLocW width) : LoopMachineState (BitVec width) F :=
  { machine with memory := fun address => some (loopValueOfWordLocW (memory address)) }

/-- Derive the memory postrelation from the input state relation. -/
theorem LoopSemStateFiniteExact.replaceMemory_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F} (hrel : state.prodRel machine)
    (memory : BitVec width → WordLocW width) :
    ({ state with memory := memory }).prodRel (loopMachineReplaceMemory machine memory) := by
  rcases hrel with ⟨hl, hg, _, hmd, hsh, hc, hb, hf, hbase, htop, hcode, hcover⟩
  exact ⟨hl, hg, fun _ => rfl, hmd, hsh, hc, hb, hf, hbase, htop, hcode, hcover⟩

/-- Canonical Store32 hook, including address/payload type failures. -/
def loopMachineStore32Exact {F : Type} (machine : LoopMachineState (BitVec 64) F) :
    LoopValue (BitVec 64) → LoopValue (BitVec 64) →
      Option (LoopMachineState (BitVec 64) F)
  | .word address, .word value =>
      (memStore32Exact (loopMachineMemoryExact machine) machine.mdomain machine.be
        address (value.setWidth 32)).map (loopMachineReplaceMemory machine)
  | _, _ => none

/-- Canonical StoreByte hook: narrowing to word8 occurs before the exact update. -/
def loopMachineStoreByteExact {F : Type} (machine : LoopMachineState (BitVec 64) F) :
    LoopValue (BitVec 64) → LoopValue (BitVec 64) →
      Option (LoopMachineState (BitVec 64) F)
  | .word address, .word value =>
      (memStoreByteAuxExact (loopMachineMemoryExact machine) machine.mdomain machine.be
        address (value.setWidth 8)).map (loopMachineReplaceMemory machine)
  | _, _ => none

theorem loopMachineStore32Exact_eq {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hrel : state.prodRel machine) (address value : BitVec 64) :
    loopMachineStore32Exact machine (.word address) (.word value) =
      (memStore32Exact state.memory state.mdomain state.be address (value.setWidth 32)).map
        (loopMachineReplaceMemory machine) := by
  obtain ⟨_, _, hm, hmd, _, _, hb, _⟩ := hrel
  simp only [loopMachineStore32Exact]
  rw [funext (loopMachineMemoryExact_eq hm), hmd, hb]

theorem loopMachineStoreByteExact_eq {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hrel : state.prodRel machine) (address value : BitVec 64) :
    loopMachineStoreByteExact machine (.word address) (.word value) =
      (memStoreByteAuxExact state.memory state.mdomain state.be address (value.setWidth 8)).map
        (loopMachineReplaceMemory machine) := by
  obtain ⟨_, _, hm, hmd, _, _, hb, _⟩ := hrel
  simp only [loopMachineStoreByteExact]
  rw [funext (loopMachineMemoryExact_eq hm), hmd, hb]

namespace LoopSemStateFiniteExact.EvaluateCases

/-- Both local/type failure branches and exact memory success/failure, assuming
only input prodRel and selection of the concrete canonical hook. -/
theorem evaluateStore32_prodRel {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hooks : LoopEvaluateHooks (BitVec 64) F) (hrel : state.prodRel machine)
    (address value : Nat)
    (hHook : hooks.store32 machine = loopMachineStore32Exact machine) :
    let exactStep := evaluate (.store32 address value) state
    let productionStep := evaluateLoop (machine.clock + 1) hooks
      (.store32 address value) machine
    storeResultRel exactStep.1 productionStep.1 ∧ exactStep.2.prodRel productionStep.2 := by
  have ha := hrel.1 address
  have hv := hrel.1 value
  cases haddr : sptLookup address state.locals <;>
    cases hvalue : sptLookup value state.locals <;>
    simp only [haddr, hvalue, Option.map_none, Option.map_some] at ha hv
  all_goals try simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue] using hrel
  all_goals
    rename_i a v
    cases a <;> cases v
    all_goals try simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue,
      loopValueOfWordLocW] using hrel
    rename_i a v
    have hh := loopMachineStore32Exact_eq hrel a v
    cases hmem : memStore32Exact state.memory state.mdomain state.be a (v.setWidth 32) with
    | none =>
        simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue,
          loopValueOfWordLocW, hHook, hh, hmem] using hrel
    | some memory =>
        have hp := replaceMemory_prodRel hrel memory
        simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue,
          loopValueOfWordLocW, hHook, hh, hmem] using hp

/-- Both local/type failure branches and exact memory success/failure, assuming
only input prodRel and selection of the concrete canonical hook. -/
theorem evaluateStoreByte_prodRel {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hooks : LoopEvaluateHooks (BitVec 64) F) (hrel : state.prodRel machine)
    (address value : Nat)
    (hHook : hooks.storeByte machine = loopMachineStoreByteExact machine) :
    let exactStep := evaluate (.storeByte address value) state
    let productionStep := evaluateLoop (machine.clock + 1) hooks
      (.storeByte address value) machine
    storeResultRel exactStep.1 productionStep.1 ∧ exactStep.2.prodRel productionStep.2 := by
  have ha := hrel.1 address
  have hv := hrel.1 value
  cases haddr : sptLookup address state.locals <;>
    cases hvalue : sptLookup value state.locals <;>
    simp only [haddr, hvalue, Option.map_none, Option.map_some] at ha hv
  all_goals try simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue] using hrel
  all_goals
    rename_i a v
    cases a <;> cases v
    all_goals try simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue,
      loopValueOfWordLocW] using hrel
    rename_i a v
    have hh := loopMachineStoreByteExact_eq hrel a v
    cases hmem : memStoreByteAuxExact state.memory state.mdomain state.be a (v.setWidth 8) with
    | none =>
        simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue,
          loopValueOfWordLocW, hHook, hh, hmem] using hrel
    | some memory =>
        have hp := replaceMemory_prodRel hrel memory
        simpa [evaluate, evaluateLoop, storeResultRel, ha, hv, haddr, hvalue,
          loopValueOfWordLocW, hHook, hh, hmem] using hp

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
