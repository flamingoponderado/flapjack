import Flapjack.Compiler.Backend.LabProps.DomainAlignment
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabSem.Arithmetic

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
/-! Original unconditional primitive alignment laws. HOL read_reg is the
source overload lambda r s.s.regs r (labSemScript77), rendered directly.
All native program/register/address values and state carriers remain generic. -/

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAlignDM {width : Nat} [NeZero width] {C F : Type}
     (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmFetch (alignDm s) = asmFetch s := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem readRegAlignDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (alignDm s).regs n = s.regs n := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updRegAlignDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updReg x y (alignDm s) = alignDm (updReg x y s) := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updMemAlignDM {width : Nat} [NeZero width] {C F : Type}
    (x : BitVec width) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updMem x y (alignDm s) = alignDm (updMem x y s) := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem binopUpdAlignDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : BinOp) (z w : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    binopUpd x y z w (alignDm s) = alignDm (binopUpd x y z w s) := by
  cases y <;> rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem regImmAlignDM {width : Nat} [NeZero width] {C F : Type}
    (r : HolRegImm width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    regImm r (alignDm s) = regImm r s := by
  cases r <;> rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem assertAlignDM {width : Nat} [NeZero width] {C F : Type}
    (b : Bool) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    assertState b (alignDm s) = alignDm (assertState b s) := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAlignSDM {width : Nat} [NeZero width] {C F : Type}
     (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmFetch (alignSdm s) = asmFetch s := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem readRegAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (alignSdm s).regs n = s.regs n := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updRegAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updReg x y (alignSdm s) = alignSdm (updReg x y s) := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updMemAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : BitVec width) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updMem x y (alignSdm s) = alignSdm (updMem x y s) := rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem binopUpdAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : BinOp) (z w : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    binopUpd x y z w (alignSdm s) = alignSdm (binopUpd x y z w s) := by
  cases y <;> rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem regImmAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (r : HolRegImm width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    regImm r (alignSdm s) = regImm r s := by
  cases r <;> rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem assertAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (b : Bool) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    assertState b (alignSdm s) = alignSdm (assertState b s) := rfl

end Flapjack.Compiler.Backend.LabProps
