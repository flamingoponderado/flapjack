import Flapjack.Pancake.Semantics.CrepSem

/-!
# Shared crepSem oracle fixture

The `baseState` (with `noNatMemory` and `noNatDomain`) used by the crepSem
parity rows in `Flapjack/Test/CrepLocalsWordLabParity.lean` and
`Flapjack/Test/CrepReplicateConstParity.lean`. The probes start from the
HOL state `s with locals := FEMPTY`; the Lean rows use this instance.
-/

namespace Flapjack.Test.Fixtures.Crep

open Flapjack

/-- Memory mapping every address to the word `0`. -/
def noNatMemory : Nat → PanWordLab Nat := fun _ => .word 0

/-- Memory domain containing no address. -/
def noNatDomain : Nat → Bool := fun _ => false

/-- Base state with empty locals/globals, matching the probe's `s with locals
:= FEMPTY`. -/
def baseState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

end Flapjack.Test.Fixtures.Crep
