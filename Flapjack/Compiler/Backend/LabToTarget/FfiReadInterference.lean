import Flapjack.Compiler.Backend.Semantics.TargetSem.FfiReads
import Flapjack.Compiler.Backend.Semantics.TargetProps.Interference

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Full original equality of the FFI-read functions after replacement of the
next-step interference oracle. No memory-read or execution premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "read_ffi_bytearrays_with_next_interfer" (words_as_type_indexed_bitvec)]
theorem readFfiBytearrays_withNextInterfer {width : Nat} [NeZero width]
    {state projection : Type} (mc : MachineConfig width state projection)
    (foo : Nat → state → state) :
    readFfiBytearraysHOL {mc with nextInterfer := foo} = readFfiBytearraysHOL mc := rfl

/-- Full original FFI-read function equality under an arbitrary oracle shift. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "read_ffi_bytearrays_shift_interfer" (words_as_type_indexed_bitvec)]
theorem readFfiBytearrays_shiftInterfer {width : Nat} [NeZero width]
    {state projection : Type} (count : Nat) (mc : MachineConfig width state projection) :
    readFfiBytearraysHOL (shiftInterfer count mc) = readFfiBytearraysHOL mc := rfl

/-- Full original FFI-read function equality after replacement of the FFI
interference oracle, with all original input byte/state carriers retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "read_ffi_bytearrays_ffi_interfer" (words_as_type_indexed_bitvec)]
theorem readFfiBytearrays_withFfiInterfer {width : Nat} [NeZero width]
    {state projection : Type} (mc : MachineConfig width state projection)
    (ffi : Nat → Nat × List (BitVec 8) × state → state) :
    readFfiBytearraysHOL {mc with ffiInterfer := ffi} = readFfiBytearraysHOL mc := rfl

end Flapjack.Compiler.Backend.LabToTarget
