import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Pancake.WordConvs.NotCreated

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-! Full original primitive and rejected comp_no_shmemop cases. The original
source guard and actual compiler equality are retained even where redundant.
Assign and Store use the literal original impossible-constructor fallback;
ShareInst is excluded by the original source guard rather than target safety. -/

/-- Full original Skip constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopSkip {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.skip) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.skip) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original Assign constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopAssign {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (name : Nat) (value : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.assign name value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.assign name value) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original Store constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopStore {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (address : WordLangExpHOL (BitVec width)) (value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.store address value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.store address value) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original Raise constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopRaise {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.raise value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.raise value) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original Break constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopBreak {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.break label) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.break label) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original Continue constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopContinue {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.continue label) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.continue label) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original Tick constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopTick {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.tick) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.tick) bs frame = (output,residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  rfl

/-- Full original ShareInst constructor case with all original common inputs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compNoShmemopShareInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (operator : WordMemOp) (name : Nat) (address : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.shareInst operator name address) : WordLangProgHOL (BitVec width)) = true)
    (_compiled : compNative conf perf (.shareInst operator name address) bs frame = (output,residual)) :
    noShmemop output = true := by
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] at guard

end Flapjack.Compiler.Backend.WordToStack.Native
