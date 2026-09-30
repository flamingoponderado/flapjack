import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.FfiHook

/-! Production/exact Loop load adapters at the actual RISC-V width. They reuse
the reviewed exact wordSem operations and the accepted production memory view.
These cross-carrier refinements have no HOL original or tag. Actual hook wiring
and the full evaluator/rebasing theorem remain separate obligations. -/
namespace Flapjack

/-- Canonical Load32 hook using the exact memory operation. A location address
fails; word results are widened to the production 64-bit payload. -/
def loopMachineLoad32Exact {F : Type} (machine : LoopMachineState (BitVec 64) F) :
    LoopValue (BitVec 64) → Option (LoopValue (BitVec 64))
  | .loc _ _ => none
  | .word address =>
      (memLoad32Exact (loopMachineMemoryExact machine) machine.mdomain machine.be address).map
        (fun value => .word (value.setWidth 64))

/-- Concrete hook agreement derived from the related memory/domain/endian
fields, without assuming a desired load result. -/
theorem loopMachineLoad32Exact_prodRel {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hrel : state.prodRel machine) (address : BitVec 64) :
    loopMachineLoad32Exact machine (.word address) =
      (memLoad32Exact state.memory state.mdomain state.be address).map
        (fun value => loopValueOfWordLocW (.word (value.setWidth 64))) := by
  have hm : loopMachineMemoryExact machine = state.memory :=
    funext (loopMachineMemoryExact_eq hrel.2.2.1)
  simp only [loopMachineLoad32Exact, hm, hrel.2.2.2.1,
    hrel.2.2.2.2.2.2.1, loopValueOfWordLocW]

/-- Canonical LoadByte hook using the exact memory operation. A location address
fails; word results are widened to the production 64-bit payload. -/
def loopMachineLoadByteExact {F : Type} (machine : LoopMachineState (BitVec 64) F) :
    LoopValue (BitVec 64) → Option (LoopValue (BitVec 64))
  | .loc _ _ => none
  | .word address =>
      (memLoadByteAuxExact (loopMachineMemoryExact machine) machine.mdomain machine.be address).map
        (fun value => .word (value.setWidth 64))

/-- Concrete hook agreement derived from the related memory/domain/endian
fields, without assuming a desired load result. -/
theorem loopMachineLoadByteExact_prodRel {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hrel : state.prodRel machine) (address : BitVec 64) :
    loopMachineLoadByteExact machine (.word address) =
      (memLoadByteAuxExact state.memory state.mdomain state.be address).map
        (fun value => loopValueOfWordLocW (.word (value.setWidth 64))) := by
  have hm : loopMachineMemoryExact machine = state.memory :=
    funext (loopMachineMemoryExact_eq hrel.2.2.1)
  simp only [loopMachineLoadByteExact, hm, hrel.2.2.2.1,
    hrel.2.2.2.2.2.2.1, loopValueOfWordLocW]

namespace LoopSemStateFiniteExact.EvaluateCases

/-- Both load cases have normal completion or Error results only. -/
def loadResultRel (exact : Option (LoopResultExact 64))
    (production : Option (LoopMachineResult (BitVec 64))) : Prop :=
  match exact, production with
  | none, none => True
  | some .error, some .error => True
  | _, _ => False

/-- Load32 correspondence with the canonical exact-memory hook selected.
Missing/location locals and read failures preserve the input relation; a
successful read uses the checked local-update relation. No target evaluation
or post-state relation is assumed. -/
theorem evaluateLoad32_prodRel {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hooks : LoopEvaluateHooks (BitVec 64) F) (hrel : state.prodRel machine)
    (address destination : Nat)
    (hHook : ∀ value, hooks.load32 machine value = loopMachineLoad32Exact machine value) :
    let exactStep := evaluate (.load32 address destination) state
    let productionStep := evaluateLoop (machine.clock + 1) hooks
      (.load32 address destination) machine
    loadResultRel exactStep.1 productionStep.1 ∧ exactStep.2.prodRel productionStep.2 := by
  have hl := hrel.1 address
  cases hlocal : sptLookup address state.locals with
  | none =>
      simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal] using hrel
  | some value =>
      cases value with
      | loc label offset =>
          simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal,
            loopValueOfWordLocW] using hrel
      | word pointer =>
          have hh := loopMachineLoad32Exact_prodRel hrel pointer
          rw [← hHook] at hh
          cases hload : memLoad32Exact state.memory state.mdomain state.be pointer with
          | none =>
              simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal,
                loopValueOfWordLocW, hh, hload] using hrel
          | some loaded =>
              have hp := setVar_prodRel hrel destination (.word (loaded.setWidth 64))
              simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal,
                loopValueOfWordLocW, hh, hload] using hp

/-- LoadByte correspondence with the canonical exact-memory hook selected.
Missing/location locals and read failures preserve the input relation; a
successful read uses the checked local-update relation. No target evaluation
or post-state relation is assumed. -/
theorem evaluateLoadByte_prodRel {F : Type}
    {state : LoopSemStateFiniteExact 64 F} {machine : LoopMachineState (BitVec 64) F}
    (hooks : LoopEvaluateHooks (BitVec 64) F) (hrel : state.prodRel machine)
    (address destination : Nat)
    (hHook : ∀ value, hooks.loadByte machine value = loopMachineLoadByteExact machine value) :
    let exactStep := evaluate (.loadByte address destination) state
    let productionStep := evaluateLoop (machine.clock + 1) hooks
      (.loadByte address destination) machine
    loadResultRel exactStep.1 productionStep.1 ∧ exactStep.2.prodRel productionStep.2 := by
  have hl := hrel.1 address
  cases hlocal : sptLookup address state.locals with
  | none =>
      simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal] using hrel
  | some value =>
      cases value with
      | loc label offset =>
          simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal,
            loopValueOfWordLocW] using hrel
      | word pointer =>
          have hh := loopMachineLoadByteExact_prodRel hrel pointer
          rw [← hHook] at hh
          cases hload : memLoadByteAuxExact state.memory state.mdomain state.be pointer with
          | none =>
              simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal,
                loopValueOfWordLocW, hh, hload] using hrel
          | some loaded =>
              have hp := setVar_prodRel hrel destination (.word (loaded.setWidth 64))
              simpa [evaluate, evaluateLoop, loadResultRel, hl, hlocal,
                loopValueOfWordLocW, hh, hload] using hp

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
