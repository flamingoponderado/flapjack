import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.LabProps.DomainAlignment
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.Semantics.WordSem

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem decClockAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    decClock (alignSdm s) = alignSdm (decClock s) := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem incPcAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    incPc (alignSdm s) = alignSdm (incPc s) := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updPcAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (p : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updPc p (alignSdm s) = alignSdm (updPc p s) := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getPcValueAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : Flapjack.Compiler.Backend.LabLang.Lab) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    getPcValue x (alignSdm s) = getPcValue x s := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getRetLocAlignSDM {width : Nat} [NeZero width] {C F : Type}
    {resultWidth : Nat} [NeZero resultWidth]
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    getRetLoc (resultWidth := resultWidth) (alignSdm s) = getRetLoc (resultWidth := resultWidth) s := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem readBytearrayMemLoadByteAuxAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    ∀ (length : Nat) (address : BitVec width), readBytearrayWordHOL address length (memLoadByteAuxExact s.memory (alignSdm s).memDomain s.be) =
      readBytearrayWordHOL address length (memLoadByteAuxExact s.memory s.memDomain s.be) := by intros; rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem writeBytearrayAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    ∀ (bytes : List (BitVec 8)) (address : BitVec width), writeBytearrayExact address bytes s.memory (alignSdm s).memDomain s.be =
      writeBytearrayExact address bytes s.memory s.memDomain s.be := by intros; rfl

end Flapjack.Compiler.Backend.LabProps
