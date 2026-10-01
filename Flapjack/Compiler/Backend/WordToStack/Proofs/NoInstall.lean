import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeReturn

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Full source move-list conclusion; every frame and formatted operand is arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wMoveAux_no_install_lem" (words_as_type_indexed_bitvec)]
theorem wMoveAuxNoInstall {width : Nat} [NeZero width]
    (xs : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    noInstall (wMoveAuxNative xs kf : HolProg width) = true := by
  have single (xy : Sum Nat Nat × Sum Nat Nat) :
      noInstall (wMoveSingleNative (width := width) xy kf) = true := by
    rcases xy with ⟨x, y⟩
    cases x <;> cases y <;> simp [wMoveSingleNative, noInstall]
  induction xs with
  | nil => simp [wMoveAuxNative, noInstall]
  | cons xy xs ih =>
    cases xs with
    | nil => exact single xy
    | cons y ys => simp [wMoveAuxNative, noInstall, single, ih]

/-- Full equality, including continuations that contain Install. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wStackLoad_no_install_lem" (words_as_type_indexed_bitvec)]
theorem wStackLoadNoInstall {width : Nat} [NeZero width]
    (ls : List (Nat × Nat)) (prog : HolProg width) :
    noInstall (wStackLoadNative ls prog) = noInstall prog := by
  induction ls with
  | nil => rfl
  | cons pair ls ih =>
    rcases pair with ⟨r, i⟩
    simp [wStackLoadNative, noInstall, ih]

/-- The universally quantified callback premise is exactly the source premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wRegWrite1_no_install_lem" (words_as_type_indexed_bitvec)]
theorem wRegWrite1NoInstall {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, noInstall (prog reg) = true) :
    noInstall (wRegWrite1Native prog r kf) = true := by
  simp only [wRegWrite1Native]
  split <;> simp [noInstall, h]

/-- The source callback premise is retained for the second temporary register. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wRegWrite2_no_install_lem" (words_as_type_indexed_bitvec)]
theorem wRegWrite2NoInstall {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, noInstall (prog reg) = true) :
    noInstall (wRegWrite2Native prog r kf) = true := by
  simp only [wRegWrite2Native]
  split <;> simp [noInstall, h]

/-- Unconditional first-projection conclusion on arbitrary cutsets and bitmaps. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wLive_no_install_lem" (words_as_type_indexed_bitvec)]
theorem wLiveNoInstall {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) :
    noInstall (wLiveNative live bs kf).1 = true := by
  simp only [wLiveNative]
  split <;> simp [noInstall]

/-- Full count/start/offset/temporary equality, with no continuation guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_no_install_lem" (words_as_type_indexed_bitvec)]
theorem stackMoveNoInstall {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) :
    noInstall (stackMoveNative n start offset i p) = noInstall p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [stackMoveNative, noInstall, ih]

/-- Full local source return-copy loop theorem on arbitrary counts and slots. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_aux_no_install" (words_as_type_indexed_bitvec)]
theorem copyRetAuxNoInstall {width : Nat} [NeZero width] (k f n : Nat) :
    noInstall (copyRetAuxNative k f n : HolProg width) = true := by
  induction n with
  | zero => simp [copyRetAuxNative, noInstall]
  | succ n ih => simp [copyRetAuxNative, listSeq, noInstall, ih]


/-- Full local source iff for both flags, independent return-list and unused
frame-tail carriers, and arbitrary native continuations. No safety premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_no_install" (words_as_type_indexed_bitvec)]
theorem copyRetNoInstall {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    noInstall (copyRetNative perf b kf vs kont) = true ↔ noInstall kont = true := by
  simp only [copyRetNative]
  split
  · rfl
  · simp only [noInstall, copyRetAuxNoInstall, Bool.true_and]
    simp only [seqStackFreeNative]
    split <;> simp [noInstall]

end Flapjack.Compiler.Backend.WordToStack.Native
