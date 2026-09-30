import Flapjack.Compiler.Backend.Semantics.StackSem.BufferWrites

/-! Kernel replay of all five original HOL observations in
`scripts/hol-probes/stacksem_buffer_write_probe.out`. The concrete fixture
overrides every observed field over an arbitrary base state; each row calls the
untagged `evaluateBufferWrite` fragment and compares the result plus the
affected buffer's position/buffer/space_left. -/

namespace Flapjack.Test.StackSemBufferWriteParity
open StackSemBufferWrites StackSemStateOps

private def fixture {C F : Type} (s : StackSemStateFiniteExact 64 C F)
    (address value : Nat) (use : Bool) : StackSemStateFiniteExact 64 C F :=
  { s with
    clock := 6
    useStack := use
    regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 64)).updateEq
      (1, .word (BitVec.ofNat 64 address))).updateEq (2, .word (BitVec.ofNat 64 value))
    codeBuffer := { position := 0, buffer := [1, 2], spaceLeft := 5 }
    dataBuffer := { position := 0, buffer := [5], spaceLeft := 2 } }

private def observeCode {C F : Type} :
    Option (Option (StackSemResult 64) × StackSemStateFiniteExact 64 C F) →
    Option (Option (StackSemResult 64) × BitVec 64 × List (BitVec 8) × Nat)
  | none => none
  | some (r, s) => some (r, s.codeBuffer.position, s.codeBuffer.buffer, s.codeBuffer.spaceLeft)

private def observeData {C F : Type} :
    Option (Option (StackSemResult 64) × StackSemStateFiniteExact 64 C F) →
    Option (Option (StackSemResult 64) × BitVec 64 × List (BitVec 64) × Nat)
  | none => none
  | some (r, s) => some (r, s.dataBuffer.position, s.dataBuffer.buffer, s.dataBuffer.spaceLeft)

variable {C F : Type} (s : StackSemStateFiniteExact 64 C F)

-- code_write_success=(NONE,0w,[1w; 2w; 4w],4)
example : observeCode (evaluateBufferWrite (.codeBufferWrite 1 2) (fixture s 2 260 true)) =
    some (none, 0, [1, 2, 4], 4) := by cbv

-- code_write_mismatch=(SOME Error,0w,[1w; 2w],5)
example : observeCode (evaluateBufferWrite (.codeBufferWrite 1 2) (fixture s 3 260 true)) =
    some (some .error, 0, [1, 2], 5) := by cbv

-- data_write_success=(NONE,0w,[5w; 300w],1)
example : observeData (evaluateBufferWrite (.dataBufferWrite 1 2) (fixture s 8 300 true)) =
    some (none, 0, [5, 300], 1) := by cbv

-- data_write_mismatch=(SOME Error,0w,[5w],2)
example : observeData (evaluateBufferWrite (.dataBufferWrite 1 2) (fixture s 9 300 true)) =
    some (some .error, 0, [5], 2) := by cbv

-- data_write_disabled=(SOME Error,0w,[5w],2)
example : observeData (evaluateBufferWrite (.dataBufferWrite 1 2) (fixture s 8 300 false)) =
    some (some .error, 0, [5], 2) := by cbv

-- The fragment returns the outer NONE sentinel for an unhandled constructor,
-- so it never substitutes Error for an unported clause.
example : evaluateBufferWrite (width := 64) (.skip) (fixture s 2 260 true) = none := rfl

/-- Closed helper checks on the exact `buffer_write` port: the code buffer uses
the 8-bit dimension factor and truncates the byte with `w2w`, the data buffer
uses the 64-bit factor, and a wrong address misses. -/
private def checks : Bool :=
  (wordSemBufferWrite ({ position := 0, buffer := [1, 2], spaceLeft := 5 } : WordSemBuffer 64 8)
      (2 : BitVec 64) ((BitVec.ofNat 64 260).setWidth 8)).isSome &&
  (wordSemBufferWrite ({ position := 0, buffer := [1, 2], spaceLeft := 5 } : WordSemBuffer 64 8)
      (3 : BitVec 64) ((BitVec.ofNat 64 260).setWidth 8)).isNone &&
  (wordSemBufferWrite ({ position := 0, buffer := [5], spaceLeft := 2 } : WordSemBuffer 64 64)
      (8 : BitVec 64) (BitVec.ofNat 64 300)).isSome &&
  (wordSemBufferWrite ({ position := 0, buffer := [5], spaceLeft := 2 } : WordSemBuffer 64 64)
      (9 : BitVec 64) (BitVec.ofNat 64 300)).isNone

#guard checks

def runChecks : IO Bool := do
  if checks then
    IO.println "PASS exact StackSem BufferWrite fragment matches original HOL branches"
    pure true
  else
    IO.println "FAIL exact StackSem BufferWrite fragment differs from original HOL branches"
    pure false

end Flapjack.Test.StackSemBufferWriteParity
