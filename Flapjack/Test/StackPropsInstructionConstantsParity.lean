import Flapjack.Compiler.Backend.StackProps.InstructionConstants

/-! Kernel replays of ten original clock/FFI-update instruction observations.
The arbitrary base state preserves independent compile and FFI carriers. -/
open Flapjack Flapjack.StackSemInst Flapjack.Compiler.Encoders.Asm

private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :=
  { s with regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq (1, .word 7)).updateEq (2, .loc 4 5), fpRegs := (HolFiniteMapExact.empty : HolFiniteMapExact Nat (BitVec 64)).updateEq (0, BitVec.ofNat 64 0xBFF0000000000000), store := HolFiniteMapExact.empty, memory := fun _ => .word 11, mdomain := fun a => a = 0, clock := 19 }

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)
example : (instHOL (.const 1 12) (fixture s)).map
    (fun t => (t.clock, t.regs.lookup 1)) = some (19, some (.word 12)) := by cbv
example : (instHOL (.const 1 12) { fixture s with clock := 0 }).map
    (fun t => (t.clock, t.regs.lookup 1)) = some (0, some (.word 12)) := by cbv
example : (instHOL (.arith (.div 1 1 3)) { fixture s with clock := 0 }).map
    (fun t => t.clock) = none := by cbv
example : (instHOL (.arith (.binop .or 1 2 (.reg 2))) (fixture s)).map
    (fun t => (t.clock, t.regs.lookup 1)) = some (19, some (.loc 4 5)) := by cbv
example : (instHOL (.mem .store 2 (.addr 1 0))
    { fixture s with regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq (1, .word 0)).updateEq (2, .loc 4 5) }).map
    (fun t => (t.clock, t.memory 0)) = some (19, .loc 4 5) := by cbv
example : (instHOL (.mem .store 2 (.addr 1 0)) (fixture s)).map
    (fun t => t.clock) = none := by cbv
example {OtherF : Type} (k : HolFfiState OtherF) : (instHOL (.const 1 12) ({ fixture s with ffi := k } : StackSemStateFiniteExact 8 C OtherF)).map
    (fun t => (t.ffi = k, t.clock, t.regs.lookup 1)) = some (True, 19, some (.word 12)) := by
  cbv
