import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production Loop `ExtCall` hook using the exact wordSem byte operations

`LoopSemStateExact.Evaluate.evaluate` is the tagged, word-polymorphic port of
HOL `loopSem$evaluate_def` and its `FFI` clause calls the tagged
`readBytearrayWordHOL`, `memLoadByteAuxExact`, and `writeBytearrayExact`
definitions.  This adapter exposes that byte-operation path through the
production `LoopEvaluateHooks.ffi` API (`LoopMachineState`, `String`,
`UInt8`, and `FfiState`).  Its API is therefore Flapjack-specific and is not
tagged as another HOL port.  The FFI call remains the production `callFfi`;
`FfiBridge` relates it to `callFFIHOL` under `FfiStateRel` and the documented
ML-string byte-range condition.

The adapter is 64-bit because it serves the current RISC-V production hook.
It reuses the exact memory byte operations rather than the older
`UInt8`-native Loop byte-array helpers.  Conversion at the boundary is via
the checked `byteToBits`/`bitsToByte` maps.
-/

namespace Flapjack

private def loopValueToWordLocW64 : LoopValue (BitVec 64) → WordLocW 64
  | .word value => .word value
  | .loc block offset => .loc block offset

private def wordLocW64ToLoopValue : WordLocW 64 → LoopValue (BitVec 64)
  | .word value => .word value
  | .loc block offset => .loc block offset

/-- The total exact word-location memory viewed by the exact `wordSem` byte
    operations.  Missing production slots use the same invalid `Loc 0 0`
    sentinel as `loopTotalMemory`; the domain predicate still decides whether
    an address is accessible. -/
def loopMachineMemoryExact (state : LoopMachineState (BitVec 64) F) :
    BitVec 64 → WordLocW 64 := fun address =>
  match state.memory address with
  | none => .loc 0 0
  | some value => loopValueToWordLocW64 value

/-- Read a byte array using the tagged exact `wordSem$mem_load_byte_aux_def`
    and `misc$read_bytearray_def`, then project `word8` bytes to production
    `UInt8`. -/
def loopReadByteArray (state : LoopMachineState (BitVec 64) F)
    (address : BitVec 64) (length : Nat) : Option (List UInt8) :=
  (readBytearrayWordHOL (byteWidth := 8) address length
    (memLoadByteAuxExact (loopMachineMemoryExact state) state.mdomain state.be)).map
      (List.map bitsToByte)

/-- Apply the tagged exact `wordSem$write_bytearray_def`, lifting the
    production bytes to HOL `word8` first. -/
def loopWriteByteArray (state : LoopMachineState (BitVec 64) F)
    (address : BitVec 64) (bytes : List UInt8) :
    LoopMachineState (BitVec 64) F :=
  let exactMemory := writeBytearrayExact address (bytes.map byteToBits)
    (loopMachineMemoryExact state) state.mdomain state.be
  { state with memory := (fun current =>
      some (wordLocW64ToLoopValue (exactMemory current))) }

/-! FLAPJACK-SPECIFIC production adapter for the `ExtCall` case of
HOL `loopSem$evaluate_def` (`loopSemScript.sml:427-440`).  The case order is
kept in the tagged exact `evaluate` above: read both input arrays from the cut
state, call the FFI, clear locals on `FFI_final`, and on `FFI_return` write the
returned bytes to the second array and retain the updated FFI state. -/
def loopMachineExtCall (state : LoopMachineState (BitVec 64) F)
    (function : FunName)
    (configurationSize configurationAddress arraySize arrayAddress : BitVec 64) :
    LoopMachineStep (BitVec 64) F :=
  match loopReadByteArray state configurationAddress configurationSize.toNat,
      loopReadByteArray state arrayAddress arraySize.toNat with
  | some configurationBytes, some arrayBytes =>
      match callFfi state.ffi (.extCall function) configurationBytes arrayBytes with
      | .final event => (some (.finalFfi event), callEnv [] state)
      | .returned newFfi newBytes =>
          (none, { loopWriteByteArray state arrayAddress newBytes with ffi := newFfi })
  | _, _ => (some .error, state)

/-- Production `LoopEvaluateHooks.ffi` adapter. `evaluateLoop` performs
`cut_state` before invoking this hook, so its live-set argument is unused. -/
def loopMachineFfiHook (function : FunName)
    (configurationSize configurationAddress arraySize arrayAddress : BitVec 64)
    (_live : List Nat) (state : LoopMachineState (BitVec 64) F) :
    LoopMachineStep (BitVec 64) F :=
  loopMachineExtCall state function configurationSize configurationAddress arraySize arrayAddress

end Flapjack
