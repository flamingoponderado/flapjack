import Flapjack.Compiler.Backend.WordToStack.NativeHandlers
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- Full source handler setup, retaining both independent unused frame carriers
and either perf branch, with no bound, safety or execution premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "PushHandler_no_shmemop" (words_as_type_indexed_bitvec)]
theorem pushHandlerNoShmemop {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (l1 l2 : Nat) (frame : Nat × β × γ) :
    noShmemop (pushHandlerNative perf l1 l2 frame : HolProg width) = true := by
  cases perf <;> simp [pushHandlerNative, noShmemop, listSeq]

/-- Exact Boolean form of the original equivalence, including false arbitrary
continuations. Both unused frame carriers remain independently polymorphic. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "PopHandler_no_shmemop" (words_as_type_indexed_bitvec)]
theorem popHandlerNoShmemop {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (frame : Nat × β × γ) (program : HolProg width) :
    noShmemop (popHandlerNative perf frame program) = noShmemop program := by
  simp [popHandlerNative, noShmemop]

/-- Full generic destination and frame theorem; both Sum payload carriers,
argument count and perf choice are unrestricted, as in the original. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "StackHandlerArgs_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackHandlerArgsNoShmemop {width : Nat} [NeZero width] {α β : Type}
    (perf : Bool) (destination : Sum α β) (argumentCount : Nat)
    (frame : Nat × Nat × Nat) :
    noShmemop (stackHandlerArgsNative perf destination argumentCount frame : HolProg width) = true := by
  simp [stackHandlerArgsNative, stackArgsNative, stackMoveNoShmemop, noShmemop]

end Flapjack.Compiler.Backend.WordToStack.Native
