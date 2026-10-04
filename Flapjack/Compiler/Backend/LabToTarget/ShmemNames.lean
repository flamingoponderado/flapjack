import Flapjack.Compiler.Backend.LabToTarget.ShmemPrefix
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack constructor invariant: a shared-memory-only accumulator stays
shared-memory-only under the original unconditional extraction. -/
private theorem shmemNamesShared {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (names : List HolFfiName) (info : List ShmemInfoNum) :
    (∀ x ∈ names, ∃ op, x = HolFfiName.sharedMem op) →
    ∀ x ∈ (getShmemInfo secs pos names info).1, ∃ op, x = HolFfiName.sharedMem op := by
  induction secs generalizing pos names info with
  | nil => intro h; simpa only [getShmemInfo] using h
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing pos names info with
    | nil => simpa only [getShmemInfo] using ih pos names info
    | cons line lines ihLines =>
      cases line with
      | label a b n => simpa only [getShmemInfo] using ihLines pos names info
      | labAsm a w bs n => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info
      | asm a bs n =>
        cases a with
        | asmi a => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info
        | cbw a b => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info
        | shareMem m r addr =>
          cases addr with
          | addr base off =>
            rcases hm : getMemopInfo m with ⟨op,nb⟩
            let entry : ShmemInfoNum :=
              {entryPc:=pos,nbytes:=nb,addrReg:=base,addrOff:=off.toNat,reg:=r,exitPc:=pos+bs.length}
            intro hn
            simp only [getShmemInfo,hm]
            refine (ihLines (pos+bs.length) (names++[HolFfiName.sharedMem op]) (info++[entry]) ?_)
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hn x hx
            · have hx' : x = .sharedMem op := List.mem_singleton.mp hx
              exact ⟨op,hx'⟩

/-- Full original existential classification: the newly appended name suffix
contains only SharedMem constructors, without validity/encoding assumptions.
All original inputs and supplied outputs remain quantified. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getShmemInfo_mappedNames {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (info : List ShmemInfoNum)
    (newFfiNames : List HolFfiName) (newInfo : List ShmemInfoNum) :
    getShmemInfo secs pos ffiNames info = (newFfiNames,newInfo) →
    ∃ l, newFfiNames = ffiNames++l ∧
      ∀ x ∈ l, ∃ op, x = HolFfiName.sharedMem op := by
  intro h
  refine ⟨(getShmemInfo secs pos [] []).1,
    (getShmemInfo_prepend secs pos ffiNames info newFfiNames newInfo h).1,?_⟩
  exact shmemNamesShared secs pos [] [] (by simp)
end Flapjack.Compiler.Backend.LabToTarget
