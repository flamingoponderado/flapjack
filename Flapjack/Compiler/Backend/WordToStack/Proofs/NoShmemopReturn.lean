import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCallCore

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Full original copy_ret preservation. The unused third frame carrier and
return-value element carrier are independent of each other and the native
continuation. HOL iff between its Boolean predicates is Bool equality here,
so the false-continuation direction is retained without a safety premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_no_shmemop" (words_as_type_indexed_bitvec)]
theorem copyRetNoShmemop {width : Nat} [NeZero width] {β γ : Type}
    (perf isHandle : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) :
    noShmemop (copyRetNative perf isHandle kf vs kont) = noShmemop kont := by
  by_cases zero : WordToStack.numStackRet kf.1 vs = 0
  · simp [copyRetNative, zero]
  · simp [copyRetNative, zero, noShmemop, copyRetAuxNoShmemop,
      seqStackFreeNative]

end Flapjack.Compiler.Backend.WordToStack.Native
