import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeReturn

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Full source move-list conclusion; every frame and formatted operand is arbitrary. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wStackLoadNoInstall {width : Nat} [NeZero width]
    (ls : List (Nat × Nat)) (prog : HolProg width) :
    noInstall (wStackLoadNative ls prog) = noInstall prog := by
  induction ls with
  | nil => rfl
  | cons pair ls ih =>
    rcases pair with ⟨r, i⟩
    simp [wStackLoadNative, noInstall, ih]

/-- The universally quantified callback premise is exactly the source premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wRegWrite1NoInstall {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, noInstall (prog reg) = true) :
    noInstall (wRegWrite1Native prog r kf) = true := by
  simp only [wRegWrite1Native]
  split <;> simp [noInstall, h]

/-- The source callback premise is retained for the second temporary register. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wRegWrite2NoInstall {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, noInstall (prog reg) = true) :
    noInstall (wRegWrite2Native prog r kf) = true := by
  simp only [wRegWrite2Native]
  split <;> simp [noInstall, h]

/-- Unconditional first-projection conclusion on arbitrary cutsets and bitmaps. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wLiveNoInstall {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) :
    noInstall (wLiveNative live bs kf).1 = true := by
  simp only [wLiveNative]
  split <;> simp [noInstall]

/-- Full count/start/offset/temporary equality, with no continuation guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackMoveNoInstall {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) :
    noInstall (stackMoveNative n start offset i p) = noInstall p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [stackMoveNative, noInstall, ih]

/-- Full local source return-copy loop theorem on arbitrary counts and slots. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem copyRetAuxNoInstall {width : Nat} [NeZero width] (k f n : Nat) :
    noInstall (copyRetAuxNative k f n : HolProg width) = true := by
  induction n with
  | zero => simp [copyRetAuxNative, noInstall]
  | succ n ih => simp [copyRetAuxNative, listSeq, noInstall, ih]


/-- Full local source iff for both flags, independent return-list and unused
frame-tail carriers, and arbitrary native continuations. No safety premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
