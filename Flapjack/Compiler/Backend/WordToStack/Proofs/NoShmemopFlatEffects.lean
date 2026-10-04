import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers
import Flapjack.Pancake.WordConvs.NotCreated

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-! Original flat-effect comp_no_shmemop cases. Each statement retains the full
original source guard and compilation equality, all constructor parameters,
assembler configuration, performance flag, bitmap state, frame and outputs.
No safety, validity, bounds or evaluator premises are added. -/

/-- Full original Move case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopMove {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (priority : Nat) (moves : List (Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.move priority moves) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.move priority moves) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [wMoveNative, wMoveAuxNoShmemop]

/-- Full original Return case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopReturn {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (label : Nat) (values : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.return label values) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.return label values) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [wStackLoadNoShmemop]
  unfold seqStackFreeNative
  split <;> rfl

/-- Full original OpCurrHeap case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopOpCurrHeap {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (op : BinOp) (dst src : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.opCurrHeap op dst src) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.opCurrHeap op dst src) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [wStackLoadNoShmemop]
  exact wRegWrite1NoShmemop _ dst frame (fun _ => rfl)

/-- Full original Set case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopSet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (name : WordStoreHOL) (value : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.set name value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.set name value) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  cases name <;> cases value
  all_goals
    simp only [compNative] at result
    rw [← result]
    first
      | rfl
      | (rw [wStackLoadNoShmemop]; rfl)

/-- Full original Get case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopGet {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (dst : Nat) (name : WordStoreHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.get dst name) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.get dst name) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  exact wRegWrite1NoShmemop _ dst frame (fun _ => rfl)

/-- Full original Alloc case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopAlloc {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (dst : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.alloc dst live) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.alloc dst live) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp [noShmemop, wLiveNoShmemop]

/-- Full original StoreConsts case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopStoreConsts {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (src bitmap codeLength dataLength : Nat)
    (constants : List (Bool × BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.storeConsts src bitmap codeLength dataLength constants) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.storeConsts src bitmap codeLength dataLength constants) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original LocValue case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopLocValue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (dst label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.locValue dst label) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.locValue dst label) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  exact wRegWrite1NoShmemop _ dst frame (fun _ => rfl)

/-- Full original Install case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (codeBuffer codeLength dataBuffer dataLength : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.install codeBuffer codeLength dataBuffer dataLength live) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.install codeBuffer codeLength dataBuffer dataLength live) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [wStackLoadNoShmemop]
  rfl

/-- Full original CodeBufferWrite case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopCodeBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (addr value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.codeBufferWrite addr value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.codeBufferWrite addr value) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [wStackLoadNoShmemop]
  rfl

/-- Full original DataBufferWrite case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopDataBufferWrite {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (addr value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.dataBufferWrite addr value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.dataBufferWrite addr value) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [wStackLoadNoShmemop]
  rfl

/-- Full original FFI case; the no-share guard is retained even where redundant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopFFI {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (name : Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.ffi name configuration configurationLength array arrayLength live) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.ffi name configuration configurationLength array arrayLength live) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

end Flapjack.Compiler.Backend.WordToStack.Native
