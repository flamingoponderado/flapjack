import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.LabProps.DomainAlignment
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabSem.SharedMemory

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem decClockAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    decClock (alignDm s) = alignDm (decClock s) := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem incPcAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    incPc (alignDm s) = alignDm (incPc s) := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updPcAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updPc p (alignDm s) = alignDm (updPc p s) := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getPcValueAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Flapjack.Compiler.Backend.LabLang.Lab) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    getPcValue x (alignDm s) = getPcValue x s := by rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getRetLocAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    {resultWidth : Nat} [NeZero resultWidth]
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    getRetLoc (resultWidth := resultWidth) (alignDm s) = getRetLoc (resultWidth := resultWidth) s := by rfl

/-- Flapjack-only equation form used to derive the original three source implications. -/
private theorem sharedProjection {width : Nat} [NeZero width] {C : Type} {F : Type}
    (m : HolMemop) (r : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    shareMemOp m r a (alignDm s) =
      (shareMemOp m r a s).map (fun pair => (pair.1,alignDm pair.2)) := by
  cases m <;> simp only [shareMemOp,shareMemLoad,shareMemStore,addrValue,alignDm,incPc,decClock]
  all_goals repeat' first | rfl | split | simp_all

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareMemOpAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (m : HolMemop) (r : Nat) (a : HolAddr width)
    (s next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (f : HolFinalEvent) (fs : HolFfiState F) (l : List (BitVec 8)) :
    (shareMemOp m r a s = none → shareMemOp m r a (alignDm s) = none) ∧
    (shareMemOp m r a s = some (.final f,next) →
      shareMemOp m r a (alignDm s) = some (.final f,alignDm next)) ∧
    (shareMemOp m r a s = some (.ret fs l,next) →
      shareMemOp m r a (alignDm s) = some (.ret fs l,alignDm next)) := by
  rw [sharedProjection]
  constructor
  · intro h; simp only [h,Option.map_none]
  · constructor
    · intro h; simp only [h,Option.map_some]
    · intro h; simp only [h,Option.map_some]

end Flapjack.Compiler.Backend.LabProps
