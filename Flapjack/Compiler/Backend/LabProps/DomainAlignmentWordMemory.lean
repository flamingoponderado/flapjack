import Flapjack.Compiler.Backend.LabProps.DomainAlignmentOperations
import Flapjack.Compiler.Backend.LabToTarget.InstMem

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

/-- Flapjack internal Boolean form of the original guarded alignment fact.
No separately named HOL declaration; no unguarded LOG2-zero equality. -/
private theorem alignedDomainWord {width : Nat} [NeZero width] (hw : goodDimindex width)
    (a : BitVec width) (d : Bool) :
    (decide (a.toNat % (width / 8) = 0) && (d && holByteAligned a)) =
      (decide (a.toNat % (width / 8) = 0) && d) := by
  by_cases ha : a.toNat % (width / 8) = 0
  · have halign : holByteAligned a = true :=
      (Flapjack.Compiler.Backend.LabToTarget.holAligned_word_iff hw a).mpr ha
    simp only [ha,decide_true,halign,Bool.and_true]
  · simp only [ha,decide_false,Bool.false_and]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem memLoadAlignDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memLoad n a (alignDm s) = alignDm (memLoad n a s) := by
  intro hw
  simp only [memLoad,addrAlignDM]
  cases haddr : addrValue a s with
  | none => rfl
  | some value =>
    simp only [alignDm,updReg,assertState,alignedDomainWord hw]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem memStoreAlignDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memStore n a (alignDm s) = alignDm (memStore n a s) := by
  intro hw
  simp only [memStore,addrAlignDM]
  cases haddr : addrValue a s with
  | none => rfl
  | some value =>
    simp only [alignDm,updMem,assertState,alignedDomainWord hw]

end Flapjack.Compiler.Backend.LabProps
