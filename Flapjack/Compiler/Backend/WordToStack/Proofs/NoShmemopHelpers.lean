import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Full source move-list preservation, with no frame or scheduler premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wMoveAux_no_shmemop_lem" (words_as_type_indexed_bitvec)]
theorem wMoveAuxNoShmemop {width : Nat} [NeZero width]
    (xs : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    noShmemop (wMoveAuxNative xs kf : HolProg width) = true := by
  have single (xy : Sum Nat Nat × Sum Nat Nat) :
      noShmemop (wMoveSingleNative (width := width) xy kf) = true := by
    rcases xy with ⟨x, y⟩
    cases x <;> cases y <;> rfl
  induction xs with
  | nil => rfl
  | cons xy rest ih =>
      cases rest with
      | nil => exact single xy
      | cons next tail => simp only [wMoveAuxNative, noShmemop, single, ih, Bool.true_and]

/-- Ordered loads preserve the complete continuation predicate, including false. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wStackLoad_no_shmemop_lem" (words_as_type_indexed_bitvec)]
theorem wStackLoadNoShmemop {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (prog : HolProg width) :
    noShmemop (wStackLoadNative loads prog) = noShmemop prog := by
  induction loads with
  | nil => rfl
  | cons load rest ih => simp [wStackLoadNative, noShmemop, ih]

/-- The only premise is the original pointwise register-continuation guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wRegWrite1_no_shmemop_lem" (words_as_type_indexed_bitvec)]
theorem wRegWrite1NoShmemop {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, noShmemop (prog reg) = true) :
    noShmemop (wRegWrite1Native prog r kf) = true := by
  by_cases reg : r / 2 < kf.1 <;> simp [wRegWrite1Native, reg, noShmemop, h]

/-- Second temporary register write has the same original pointwise guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wRegWrite2_no_shmemop_lem" (words_as_type_indexed_bitvec)]
theorem wRegWrite2NoShmemop {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, noShmemop (prog reg) = true) :
    noShmemop (wRegWrite2Native prog r kf) = true := by
  by_cases reg : r / 2 < kf.1 <;> simp [wRegWrite2Native, reg, noShmemop, h]

/-- Arbitrary source cutsets and full bitmap state; no validity premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wLive_no_shmemop_lem" (words_as_type_indexed_bitvec)]
theorem wLiveNoShmemop {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) :
    noShmemop (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative
  split <;> rfl

/-- All source offsets and counts preserve the full continuation predicate. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_no_shmemop_lem" (words_as_type_indexed_bitvec)]
theorem stackMoveNoShmemop {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) :
    noShmemop (stackMoveNative n start offset i p) = noShmemop p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [stackMoveNative, noShmemop, ih]

end Flapjack.Compiler.Backend.WordToStack.Native
