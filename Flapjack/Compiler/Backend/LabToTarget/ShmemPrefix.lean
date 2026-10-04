import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack structural transport for arbitrary accumulator prefixes. Unlike
instruction enumeration, this law needs no encoding or label-validity guard. -/
private theorem shmemPrefix {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) (ffis1 ffis2 : List HolFfiName)
    (info1 info2 : List ShmemInfoNum) :
    getShmemInfo secs pos (ffis1++ffis2) (info1++info2) =
      (ffis1++(getShmemInfo secs pos ffis2 info2).1,
       info1++(getShmemInfo secs pos ffis2 info2).2) := by
  induction secs generalizing pos ffis1 ffis2 info1 info2 with
  | nil => simp only [getShmemInfo]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing pos ffis1 ffis2 info1 info2 with
    | nil => simpa only [getShmemInfo] using ih pos ffis1 ffis2 info1 info2
    | cons line lines ihLines =>
      cases line with
      | label a b n =>
        simpa only [getShmemInfo] using ihLines pos ffis1 ffis2 info1 info2
      | labAsm a w bs n =>
        simpa only [getShmemInfo] using ihLines (pos+bs.length) ffis1 ffis2 info1 info2
      | asm a bs n =>
        cases a with
        | asmi a =>
          simpa only [getShmemInfo] using ihLines (pos+bs.length) ffis1 ffis2 info1 info2
        | cbw a b =>
          simpa only [getShmemInfo] using ihLines (pos+bs.length) ffis1 ffis2 info1 info2
        | shareMem m r addr =>
          cases addr with
          | addr base off =>
            rcases hm : getMemopInfo m with ⟨name,nb⟩
            let entry : ShmemInfoNum :=
              {entryPc:=pos,nbytes:=nb,addrReg:=base,addrOff:=off.toNat,reg:=r,exitPc:=pos+bs.length}
            simpa only [getShmemInfo,hm,List.append_assoc,entry] using
              ihLines (pos+bs.length) ffis1 (ffis2++[.sharedMem name]) info1 (info2++[entry])

/-- Full original APPEND theorem: arbitrary source code and accumulator
splits, preserving the supplied result tuple and all three source premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getShmemInfo_append {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (shmemInfo : List ShmemInfoNum)
    (ffis1 ffis2 : List HolFfiName) (info1 info2 : List ShmemInfoNum)
    (newFfiNames : List HolFfiName) (newShmemInfo : List ShmemInfoNum) :
    getShmemInfo secs pos ffiNames shmemInfo = (newFfiNames,newShmemInfo) ∧
    ffiNames = ffis1++ffis2 ∧ shmemInfo = info1++info2 →
    newFfiNames = ffis1++(getShmemInfo secs pos ffis2 info2).1 ∧
    newShmemInfo = info1++(getShmemInfo secs pos ffis2 info2).2 := by
  rintro ⟨h,rfl,rfl⟩
  rw [shmemPrefix] at h
  exact ⟨(congrArg Prod.fst h).symm,(congrArg Prod.snd h).symm⟩

/-- Full original PREPEND theorem, with the original output equality premise;
it follows from unconditional prefix transport, including invalid labels. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getShmemInfo_prepend {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (shmemInfo : List ShmemInfoNum)
    (newFfiNames : List HolFfiName) (newShmemInfo : List ShmemInfoNum) :
    getShmemInfo secs pos ffiNames shmemInfo = (newFfiNames,newShmemInfo) →
    newFfiNames = ffiNames++(getShmemInfo secs pos [] []).1 ∧
    newShmemInfo = shmemInfo++(getShmemInfo secs pos [] []).2 := by
  intro h
  exact getShmemInfo_append secs pos ffiNames shmemInfo ffiNames [] shmemInfo []
    newFfiNames newShmemInfo ⟨h,by simp,by simp⟩
end Flapjack.Compiler.Backend.LabToTarget
