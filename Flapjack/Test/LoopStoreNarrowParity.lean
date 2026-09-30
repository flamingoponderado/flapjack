import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.StoreNarrow

/-! Adapter regression checks. Store32 numeric expectations reuse existing
HOL-captured rows cited by LoopSemWordMemExactParity; byte checks exercise
narrowing/endian transport. No new oracle rows or executed-bundle claim. -/
namespace Flapjack.Test.LoopStoreNarrowParity
open Flapjack LoopSemStateFiniteExact.EvaluateCases

private def machine (be : Bool := false) : LoopMachineState (BitVec 64) Unit :=
  { locals := fun _ => none, globals := fun _ => none,
    memory := fun _ => some (.word 0), mdomain := fun a => a == 0,
    shMdomain := fun _ => false, clock := 7, code := [], be := be,
    ffi := trivialFfiState Unit (), baseAddr := 0, topAddr := 0 }

#guard (loopMachineStore32Exact machine (.word 0) (.word 0x111223344)).bind
  (fun m => m.memory 0) == some (.word 0x11223344)
#guard (loopMachineStore32Exact (machine true) (.word 0) (.word 0x11223344)).bind
  (fun m => m.memory 0) == some (.word 0x1122334400000000)
#guard (loopMachineStore32Exact machine (.word 4) (.word 0x11223344)).bind
  (fun m => m.memory 0) == some (.word 0x1122334400000000)
#guard (loopMachineStore32Exact machine (.word 2) (.word 1)).isNone
#guard (loopMachineStore32Exact machine (.word 8) (.word 1)).isNone
#guard (loopMachineStore32Exact { machine with memory := fun _ => some (.loc 0 0) }
  (.word 0) (.word 1)).isNone
#guard (loopMachineStore32Exact machine (.loc 0 0) (.word 1)).isNone
#guard (loopMachineStore32Exact machine (.word 0) (.loc 0 0)).isNone
#guard (loopMachineStore32Exact machine (.word 0) (.word 1)).bind
  (fun m => m.memory 8) == some (.word 0)
#guard (loopMachineStoreByteExact machine (.word 1) (.word 0x1ee)).bind
  (fun m => m.memory 0) == some (.word 0xee00)
#guard (loopMachineStoreByteExact (machine true) (.word 1) (.word 0xee)).bind
  (fun m => m.memory 0) == some (.word 0x00ee000000000000)
#guard (loopMachineStoreByteExact machine (.word 8) (.word 1)).isNone
#guard (loopMachineStoreByteExact { machine with memory := fun _ => none }
  (.word 0) (.word 1)).isNone
#guard (loopMachineStoreByteExact machine (.loc 0 0) (.word 1)).isNone
#guard (loopMachineStoreByteExact machine (.word 0) (.loc 0 0)).isNone
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
