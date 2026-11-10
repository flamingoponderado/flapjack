import Flapjack.LoopFfi

/-!
# Shared loopSem oracle fixture

The `returningState` fixture used by the loopSem shared-memory parity rows in
`Flapjack/Test/LoopShMemLoadParity.lean` and `Flapjack/Test/LoopShMemStoreParity.lean`.
It models the original `loopSem` state whose FFI oracle returns the bytes it
receives unchanged.
-/

namespace Flapjack.Test.Fixtures.Loop

open Flapjack

/-- A loopSem FFI state whose oracle returns its input bytes unchanged. -/
def returningState (shared : Bool) : LoopFfiState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => shared
    byteAlign := id
    clock := 10
    bigEndian := false
    baseAddress := 0
    topAddress := 0
    ffi :=
      { oracle := fun _ state _ bytes => .returned state bytes
        state := ()
        ioEvents := [] }
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes => bytes.head?.getD 0 |>.toNat
    valueToNat := id }

end Flapjack.Test.Fixtures.Loop
