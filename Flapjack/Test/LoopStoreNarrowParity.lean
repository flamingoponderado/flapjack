import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.StoreNarrow

/-! Direct original loopSem evaluate_def observations at width64:
`scripts/hol-probes/loop_sem_store_narrow_probe.out` provides one named row for
every guard below. The probe registers the ORIGINAL evaluate_def in HOL's
compset and runs Store32/StoreByte, including w2w narrowing and endian updates.
Error rows observe SOME Error; successful rows observe returned memory/clock.
The production hook's missing-memory case totalizes to Loc0 0, so its matching
original row uses that sentinel. No new executed hook-bundle claim. -/
namespace Flapjack.Test.LoopStoreNarrowParity
open Flapjack LoopSemStateFiniteExact.EvaluateCases

private def machine (be : Bool := false) : LoopMachineState (BitVec 64) Unit :=
  { locals := fun _ => none, globals := fun _ => none,
    memory := fun _ => some (.word 0), mdomain := fun a => a == 0,
    shMdomain := fun _ => false, clock := 7, code := [], be := be,
    ffi := trivialFfiState Unit (), baseAddr := 0, topAddr := 0 }

-- Original HOL row: store32_narrow
#guard (loopMachineStore32Exact machine (.word 0) (.word 0x111223344)).bind
  (fun m => m.memory 0) == some (.word 0x11223344)
-- Original HOL row: store32_big
#guard (loopMachineStore32Exact (machine true) (.word 0) (.word 0x11223344)).bind
  (fun m => m.memory 0) == some (.word 0x1122334400000000)
-- Original HOL row: store32_upper
#guard (loopMachineStore32Exact machine (.word 4) (.word 0x11223344)).bind
  (fun m => m.memory 0) == some (.word 0x1122334400000000)
-- Original HOL row: store32_unaligned
#guard (loopMachineStore32Exact machine (.word 2) (.word 1)).isNone
-- Original HOL row: store32_domain
#guard (loopMachineStore32Exact machine (.word 8) (.word 1)).isNone
-- Original HOL row: store32_memory_loc
#guard (loopMachineStore32Exact { machine with memory := fun _ => some (.loc 0 0) }
  (.word 0) (.word 1)).isNone
-- Original HOL row: store32_address_loc
#guard (loopMachineStore32Exact machine (.loc 0 0) (.word 1)).isNone
-- Original HOL row: store32_value_loc
#guard (loopMachineStore32Exact machine (.word 0) (.loc 0 0)).isNone
-- Original HOL row: store32_other
#guard (loopMachineStore32Exact machine (.word 0) (.word 1)).bind
  (fun m => m.memory 8) == some (.word 0)
-- Original HOL row: storeByte_narrow
#guard (loopMachineStoreByteExact machine (.word 1) (.word 0x1ee)).bind
  (fun m => m.memory 0) == some (.word 0xee00)
-- Original HOL row: storeByte_big
#guard (loopMachineStoreByteExact (machine true) (.word 1) (.word 0xee)).bind
  (fun m => m.memory 0) == some (.word 0x00ee000000000000)
-- Original HOL row: storeByte_domain
#guard (loopMachineStoreByteExact machine (.word 8) (.word 1)).isNone
-- Original HOL row: storeByte_memory_loc
-- Absent production slot is the exact Loc0 0 sentinel.
#guard (loopMachineStoreByteExact { machine with memory := fun _ => none }
  (.word 0) (.word 1)).isNone
-- Original HOL row: storeByte_address_loc
#guard (loopMachineStoreByteExact machine (.loc 0 0) (.word 1)).isNone
-- Original HOL row: storeByte_value_loc
#guard (loopMachineStoreByteExact machine (.word 0) (.loc 0 0)).isNone
-- Original HOL row: storeByte_clock
#guard (loopMachineStoreByteExact machine (.word 0) (.word 1)).map (·.clock) == some 7

example {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {m : LoopMachineState (BitVec 64) F} (h : s.prodRel m)
    (hooks : LoopEvaluateHooks (BitVec 64) F) (a v : Nat)
    (hh : hooks.store32 m = loopMachineStore32Exact m) :
    let x := LoopSemStateFiniteExact.evaluate (.store32 a v) s
    let y := evaluateLoop (m.clock + 1) hooks (.store32 a v) m
    storeResultRel x.1 y.1 ∧ x.2.prodRel y.2 := evaluateStore32_prodRel hooks h a v hh
example {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {m : LoopMachineState (BitVec 64) F} (h : s.prodRel m)
    (hooks : LoopEvaluateHooks (BitVec 64) F) (a v : Nat)
    (hh : hooks.storeByte m = loopMachineStoreByteExact m) :
    let x := LoopSemStateFiniteExact.evaluate (.storeByte a v) s
    let y := evaluateLoop (m.clock + 1) hooks (.storeByte a v) m
    storeResultRel x.1 y.1 ∧ x.2.prodRel y.2 := evaluateStoreByte_prodRel hooks h a v hh

def runChecks : IO Bool := do
  IO.println "PASS canonical Loop Store32/StoreByte hooks and conditional full cases (bundle wiring open)"
  return true
end Flapjack.Test.LoopStoreNarrowParity
