import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock

/-! Original stackprops_shared_memory_clock_probe.out: full native returned,
terminal, domain-failure and non-word cases. Clock update proofs retain the
whole state; numerical observations are kernel regression evidence. -/
namespace Flapjack.Test.StackPropsSharedMemoryClockParity
open Flapjack StackSemShMem StackPropsSharedMemoryClock

private abbrev W := WordLocW 64

private def incFfi : HolFfiState Nat :=
  { oracle := fun _ st _ bytes => .ret (st + 1) (bytes.map (· + 1)), ffiState := 0,
    ioEvents := [] }

private def divFfi : HolFfiState Nat :=
  { oracle := fun _ _ _ _ => .final .diverged, ffiState := 0, ioEvents := [] }

private def s0 : StackSemStateFiniteExact 64 Unit Nat where
  regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat W).updateEq
    (3, .word 0x1122)).updateEq (4, .loc 1 0)
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackSpace := 0
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun a => a = 8
  bitmaps := []
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [], [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  useStack := false
  useStore := false
  useAlloc := false
  clock := 37
  code := .ln
  ffi := incFfi
  ffiSaveRegs := fun _ => false
  be := false


private def observe (p : Option (StackSemResult 64) × StackSemStateFiniteExact 64 Unit Nat) :
    Nat × Nat × Nat × Nat × Nat :=
  ((match p.1 with | none => 0 | some .error => 1 | some (.finalFFI _) => 2 | _ => 3),
    p.2.clock, p.2.ffi.ffiState, p.2.ffi.ioEvents.length,
    match p.2.regs.lookup 5 with | some (.word w) => w.toNat | _ => 0)

private theorem store : observe (shMemOp .store 3 8 (s0)) = (0, 37, 1, 1, 0) := by
  decide +kernel

private theorem load : observe (shMemOp .load 5 8 (s0)) = (0, 37, 1, 1, 72340172838076681) := by
  decide +kernel

private theorem store8 : observe (shMemOp .store8 3 9 (s0)) = (0, 37, 1, 1, 0) := by
  decide +kernel

private theorem load8 : observe (shMemOp .load8 5 9 (s0)) = (0, 37, 1, 1, 72340172838076682) := by
  decide +kernel

private theorem store16 : observe (shMemOp .store16 3 10 (s0)) = (0, 37, 1, 1, 0) := by
  decide +kernel

private theorem load16 : observe (shMemOp .load16 5 10 (s0)) = (0, 37, 1, 1, 72340172838076683) := by
  decide +kernel

private theorem store32 : observe (shMemOp .store32 3 12 (s0)) = (0, 37, 1, 1, 0) := by
  decide +kernel

private theorem load32 : observe (shMemOp .load32 5 12 (s0)) = (0, 37, 1, 1, 72340172838076685) := by
  decide +kernel

private theorem load_outside : observe (shMemOp .load 5 16 (s0)) = (1, 37, 0, 0, 0) := by
  decide +kernel

private theorem store8_outside : observe (shMemOp .store8 3 17 (s0)) = (1, 37, 0, 0, 0) := by
  decide +kernel

private theorem load_word_unaligned : observe (shMemOp .load 5 9 (s0)) = (1, 37, 0, 0, 0) := by
  decide +kernel

private theorem store_word_unaligned : observe (shMemOp .store 3 9 (s0)) = (1, 37, 0, 0, 0) := by
  decide +kernel

private theorem load_final : observe (shMemOp .load 5 8 ({ s0 with ffi := divFfi })) = (2, 37, 0, 0, 0) := by
  decide +kernel

private theorem store_final : observe (shMemOp .store 3 8 ({ s0 with ffi := divFfi })) = (2, 37, 0, 0, 0) := by
  decide +kernel

private theorem store_loc : observe (shMemOp .store 4 8 (s0)) = (1, 37, 0, 0, 0) := by
  decide +kernel

/-- Actual full dispatch theorem application over arbitrary words and states. -/
example {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (r : Nat) (a : BitVec width)
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    shMemOp op r a { s with clock := k } =
      Prod.map id (fun s => { s with clock := k }) (shMemOp op r a s) :=
  shMemOpWithClock op r a s k

def runChecks : IO Bool := do
  IO.println "PASS original shared-memory clock commutation (15 kernel observations/full native theorem)"
  pure true

end Flapjack.Test.StackPropsSharedMemoryClockParity
