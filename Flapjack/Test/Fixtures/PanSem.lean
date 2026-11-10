import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiCore

/-!
# Shared PanSem oracle fixtures

The `sourceState` (with its `exactMemory` and `localsWordX` helpers) used by the
PanSem `Store`/`Store32` error parity rows in
`Flapjack/Test/PanSemStoreErrorExactParity.lean` and
`Flapjack/Test/PanSemStore32ErrorExactParity.lean`. Local `x` holds a word and
the memory maps every address to a word; the store domain is the caller's
`domain`.
-/

namespace Flapjack.Test.Fixtures.PanSem

open Flapjack
open Flapjack.RiscV

/-- Memory mapping every address to a word. -/
def exactMemory : Word 64 → Option (PanValue (Word 64)) := fun _ => some (.word 0)

/-- Local environment where only `x` is bound, to the word `3`. -/
def localsWordX : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State-owned source state used by the memory guards: local `x` holds a word
    and the store domain contains address `8` only when `domain` says so. -/
def sourceState (domain : Word 64 → Bool) : PanSemState (Word 64) (FfiState Unit) :=
  { locals := localsWordX
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := exactMemory
    memaddrs := domain
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

/-- Store domain containing only address `8`. -/
def exactDomain : Word 64 → Bool := fun address => address == 8

/-- State-owned source state used by the `Assign`/`If` guards: local `x` holds a
    word, the store domain contains address `8`, and the clock is 5. -/
def assignSourceState : PanSemState (Word 64) (FfiState Unit) :=
  { locals := localsWordX
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := exactMemory
    memaddrs := exactDomain
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

end Flapjack.Test.Fixtures.PanSem
