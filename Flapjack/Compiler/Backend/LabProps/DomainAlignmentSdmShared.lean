import Flapjack.Compiler.Backend.LabProps.DomainAlignmentOperations
import Flapjack.Compiler.Backend.LabSem.SharedMemory
import Flapjack.Compiler.Backend.LabToTarget.InstMem

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alignSdmAligned {width : Nat} [NeZero width] {C F : Type}
    (x : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width →
    ((s.sharedMemDomain x = true ∧ x.toNat % (width / 8) = 0) ↔
      (alignSdm s).sharedMemDomain x = true) := by
  intro hw
  simp only [alignSdm, Bool.and_eq_true]
  change (_ ∧ _) ↔ (_ ∧ holAligned (holLOG2 (width / 8)) x = true)
  rw [holAligned_word_iff hw]

/-- Flapjack-only Boolean guard equality used to prove the original shared-memory laws. -/
private theorem sharedGuard {width : Nat} [NeZero width] (hw : goodDimindex width)
    (size : Nat) (x : BitVec width) (domain : BitVec width → Bool) :
    (if size = 0 then x.toNat % (width / 8) == 0 && (domain x && holByteAligned x)
      else domain (riscvByteAlignHOL x) && holByteAligned (riscvByteAlignHOL x)) =
    (if size = 0 then x.toNat % (width / 8) == 0 && domain x
      else domain (riscvByteAlignHOL x)) := by
  by_cases hn : size = 0
  · simp only [hn, if_true]
    by_cases hx : x.toNat % (width / 8) = 0
    · have ha : holByteAligned x = true := (holAligned_word_iff hw x).2 hx
      simp [hx, ha]
    · have hb : (x.toNat % (width / 8) == 0) = false := by simpa using hx
      simp only [hb, Bool.false_and]
  · simp only [hn, if_false]
    have hm : (holByteAlign x).toNat % (width / 8) = 0 := by
      rw [holByteAlign_toNat hw]
      exact Nat.mul_mod_left _ _
    have ha : holByteAligned (riscvByteAlignHOL x) = true := by
      rw [riscvByteAlignHOL_eq hw]
      exact (holAligned_word_iff hw _).2 hm
    simp [ha]

/-- Flapjack-only stronger transition equation; the tagged theorem below retains HOL's conjunction. -/
private theorem loadProjection {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (r : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (n : Nat) :
    shareMemLoad r a (alignSdm s) n =
      (shareMemLoad r a s n).map (fun pair => (pair.1, alignSdm pair.2)) := by
  simp only [shareMemLoad,addrAlignSDM]
  simp only [alignSdm, sharedGuard hw]
  all_goals repeat' first | rfl | split

private theorem storeProjection {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (r : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (n : Nat) :
    shareMemStore r a (alignSdm s) n =
      (shareMemStore r a s n).map (fun pair => (pair.1, alignSdm pair.2)) := by
  simp only [shareMemStore,addrAlignSDM]
  simp only [alignSdm, sharedGuard hw,incPc,decClock]
  all_goals repeat' first | rfl | split

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareMemLoadAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : HolAddr width) (s next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (n : Nat) (res : HolFfiResult F) :
    goodDimindex width →
    (shareMemLoad r a (alignSdm s) n = none ↔ shareMemLoad r a s n = none) ∧
    (shareMemLoad r a s n = some (res, next) →
      shareMemLoad r a (alignSdm s) n = some (res, alignSdm next)) := by
  intro hw
  rw [loadProjection hw]
  constructor
  · cases shareMemLoad r a s n <;> simp
  · intro h
    simp only [h, Option.map_some]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareMemStoreAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : HolAddr width) (s next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (n : Nat) (res : HolFfiResult F) :
    goodDimindex width →
    (shareMemStore r a (alignSdm s) n = none ↔ shareMemStore r a s n = none) ∧
    (shareMemStore r a s n = some (res, next) →
      shareMemStore r a (alignSdm s) n = some (res, alignSdm next)) := by
  intro hw
  rw [storeProjection hw]
  constructor
  · cases shareMemStore r a s n <;> simp
  · intro h
    simp only [h, Option.map_some]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareMemOpAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (m : HolMemop) (r : Nat) (a : HolAddr width)
    (s next : Flapjack.Compiler.Backend.LabSem.State width C F) (res : HolFfiResult F) :
    goodDimindex width →
    (shareMemOp m r a s = none ↔ shareMemOp m r a (alignSdm s) = none) ∧
    (shareMemOp m r a s = some (res, next) →
      shareMemOp m r a (alignSdm s) = some (res, alignSdm next)) := by
  intro hw
  cases m <;> simp only [shareMemOp]
  all_goals first
    | exact ⟨(shareMemLoadAlignSDM r a s next _ res hw).1.symm,
        (shareMemLoadAlignSDM r a s next _ res hw).2⟩
    | exact ⟨(shareMemStoreAlignSDM r a s next _ res hw).1.symm,
        (shareMemStoreAlignSDM r a s next _ res hw).2⟩

end Flapjack.Compiler.Backend.LabProps
