module

public import Flapjack.PanValueFfiCore
public import Flapjack.RiscV.PanMemory

-- Checks below run compiled code from these modules.
public meta import Flapjack.PanValues
public meta import Flapjack.PanValueFfiCore
public meta import Flapjack.CakeParser.SexpPrint
public meta import Flapjack.RiscV.PanMemory
@[expose] public section

/-!
Fixtures for the stateful FFI tests: a little-endian oracle that returns a
fixed word for shared reads and echoes write payloads, with its context,
handlers and memory. The checks of the stepped evaluator built on these
fixtures moved to stepped-flapjack (#1251).
-/

namespace Flapjack

open RiscV

def statefulTestDecodeLittleEndian : List UInt8 → Nat → Nat
  | [], _ => 0
  | byte :: bytes, index => byte.toNat * 256 ^ index +
      statefulTestDecodeLittleEndian bytes (index + 1)

def statefulTestWordToBytes (value : Word 64) (bigEndian : Bool) : List UInt8 :=
  let bytes := (List.range 8).map (fun index =>
    UInt8.ofNat ((value.toNat / 256 ^ index) % 256))
  if bigEndian then bytes.reverse else bytes

def statefulTestWordOfBytes (bigEndian : Bool) (bytes : List UInt8) : Word 64 :=
  let bytes := if bigEndian then bytes.reverse else bytes
  BitVec.ofNat 64 (statefulTestDecodeLittleEndian bytes 0)

def statefulTestOracle : FfiOracle Unit :=
  fun name state _ bytes =>
    match name with
    | .sharedMem .mappedRead =>
        .returned state (statefulTestWordToBytes (BitVec.ofNat 64 0x42) false)
    | .sharedMem .mappedWrite => .returned state bytes
    | .extCall _ => .returned state bytes

def statefulTestFfiState : FfiState Unit :=
  { oracle := statefulTestOracle, state := (), ioEvents := [] }

def statefulTestContext : PanValueFfiContext (Word 64) :=
  { sharedDomain := fun _ => true
    byteAlign := fun address => panRiscVByteAlign (BitVec.ofNat 64 8) address
    bigEndian := false
    wordToBytes := statefulTestWordToBytes
    wordOfBytes := statefulTestWordOfBytes
    wordToByte := fun value => UInt8.ofNat value.toNat
    byteToWord := fun value => BitVec.ofNat 64 value.toNat
    valueToNat := fun value => value.toNat }

def statefulTestHandler : PanValueStatefulFfiHandler (Word 64) Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def statefulTestPrimitive : PanPrimitiveHandler (Word 64) :=
  fun _ _ => none

#guard panValuePayloadWithinLimit []
  (.rStruct [.word (BitVec.ofNat 64 1), .word (BitVec.ofNat 64 2)])

def statefulTestMemory : Word 64 → Option (PanValue (Word 64)) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x0000000000000042))
    else none

def statefulExtCallWriteFailureAccess : PanValueMemoryAccess (Word 64) :=
  { panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel with
    readByte := fun _ _ _ _ => some 0
    storeByte := fun _ memory _ address value =>
      if address == BitVec.ofNat 64 8 then
        some (fun current =>
          if current == address then some (.word value) else memory current)
      else none }

def statefulExtCallWriteFailureOracle : FfiOracle Unit :=
  fun name state _ _ =>
    match name with
    | .extCall _ => .returned state [UInt8.ofNat 1, UInt8.ofNat 2]
    | _ => .returned state []

def statefulExtCallWriteFailureFfi : FfiState Unit :=
  { oracle := statefulExtCallWriteFailureOracle, state := (), ioEvents := [] }

#guard
  match panValueFfiExtCall statefulExtCallWriteFailureAccess statefulTestContext
      (fun address =>
        if address == BitVec.ofNat 64 8 then some (.word 0) else none)
      (BitVec.ofNat 64 8) statefulExtCallWriteFailureFfi "writeFailure"
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 2) with
  | some (.returned memory _) =>
      (match memory (BitVec.ofNat 64 8) with
        | some (.word value) => value == BitVec.ofNat 64 1
        | _ => false) &&
        (memory (BitVec.ofNat 64 9)).isNone
  | _ => false

def statefulTestFinalOracle : FfiOracle Unit :=
  fun _ _ _ _ => .final .failed

def statefulTestFinalState : FfiState Unit :=
  { oracle := statefulTestFinalOracle, state := (), ioEvents := [] }

end Flapjack
