import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Instructions

namespace Flapjack.WordToStackProofs.AllocArgs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific induction calculation inside the original Move case;
no standalone HOL theorem names this arbitrary formatted-move fact. -/
theorem moveAuxAllocArg {width : Nat} [NeZero width]
    (xs : List (Sum Nat Nat × Sum Nat Nat)) (frame : Nat × Nat × Nat) :
    allocArg (wMoveAuxNative xs frame : HolProg width) := by
  have single (xy : Sum Nat Nat × Sum Nat Nat) :
      allocArg (wMoveSingleNative (width := width) xy frame) := by
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> trivial
  induction xs with
  | nil => trivial
  | cons xy xs ih =>
      cases xs with
      | nil => exact single xy
      | cons y ys => simpa [wMoveAuxNative, allocArg, single] using ih

/-- Flapjack-specific first-projection calculation within the original Alloc
and Call cases; the full cutsets, bitmap and frame arguments remain arbitrary. -/
theorem liveAllocArg {width : Nat} [NeZero width]
    (live : WordLangCutsetsHOL) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) : allocArg (wLiveNative live bs frame).1 := by
  simp only [wLiveNative]
  split <;> trivial

/-- Full original Skip case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgSkip {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.skip) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Move case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgMove {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (priority : Nat) (moves : List (Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.move priority moves) bs frame).1 := by
  subst perf
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ frame

/-- Full original Assign case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgAssign {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.assign v exp) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Get case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgGet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (name : WordStoreHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.get v name) bs frame).1 := by
  subst perf
  simp only [compNative]
  exact write1AllocArg _ v frame (fun _ => trivial)

/-- Full original Set case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgSet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (name : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.set name exp) bs frame).1 := by
  subst perf
  cases name <;> cases exp <;> simp only [compNative]
  all_goals first | trivial | exact (loadAllocArg _ _).2 (by trivial)

/-- Full original Store case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgStore {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (exp : WordLangExpHOL (BitVec width)) (v : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.store exp v) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Alloc case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgAlloc {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.alloc v live) bs frame).1 := by
  subst perf
  simp only [compNative, allocArg]
  exact ⟨liveAllocArg live bs frame, True.intro⟩

/-- Full original StoreConsts case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgStoreConsts {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 r3 r4 : Nat) (ws : List (Bool × BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.storeConsts r1 r2 r3 r4 ws) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Raise case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgRaise {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.raise v) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Return case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgReturn {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v : Nat) (vs : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.return v vs) bs frame).1 := by
  subst perf
  simp only [compNative]
  apply (loadAllocArg _ _).2
  simp only [seqStackFreeNative]
  split <;> trivial

/-- Full original Break case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgBreak {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.break label) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Continue case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgContinue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.continue label) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original Tick case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgTick {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.tick) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

/-- Full original OpCurrHeap case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgOpCurrHeap {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (op : BinOp) (v src : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.opCurrHeap op v src) bs frame).1 := by
  subst perf
  simp only [compNative]
  apply (loadAllocArg _ _).2
  exact write1AllocArg _ v frame (fun _ => trivial)

/-- Full original LocValue case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgLocValue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (v label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.locValue v label) bs frame).1 := by
  subst perf
  simp only [compNative]
  exact write1AllocArg _ v frame (fun _ => trivial)

/-- Full original Install case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 r3 r4 : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.install r1 r2 r3 r4 live) bs frame).1 := by
  subst perf
  simp only [compNative]
  exact (loadAllocArg _ _).2 (by trivial)

/-- Full original CodeBufferWrite case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgCodeBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.codeBufferWrite r1 r2) bs frame).1 := by
  subst perf
  simp only [compNative]
  exact (loadAllocArg _ _).2 (by trivial)

/-- Full original DataBufferWrite case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgDataBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (r1 r2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.dataBufferWrite r1 r2) bs frame).1 := by
  subst perf
  simp only [compNative]
  exact (loadAllocArg _ _).2 (by trivial)

/-- Full original Ffi case of `word_to_stack_alloc_arg`, with all constructor
fields and only the original false-performance guard; no compiler result premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgFfi {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (name : Basis.Pure.MlString.MlString) (r1 r2 r3 r4 : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.ffi name r1 r2 r3 r4 live) bs frame).1 := by
  subst perf
  simp only [compNative]
  trivial

end Flapjack.WordToStackProofs.AllocArgs
