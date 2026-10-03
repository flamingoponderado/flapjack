import Flapjack.Misc.FindIndex.Shift
import Flapjack.Compiler.Backend.LabToTarget.ShmemCorrectness
namespace Flapjack.Test.MiscFindIndexShiftParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
example {α : Type} [DecidableEq α] (values : List α) (target : α) (offset index : Nat) :
    findIndex target values offset = some index → index ≥ offset ∧
      ∀ nextOffset, findIndex target values nextOffset = some (index-offset+nextOffset) :=
  findIndexShift values target offset index
example : findIndex 13 [7,13] 10 = some 11 := by decide
example : findIndex 13 [7,13] 99 = some (11-10+99) := by decide
example : findIndex 7 [7,7] 10 = some 10 ∧ findIndex 7 [7,7] 99 = some 99 := by decide
example : findIndex 7 [] 10 = none := by decide
example : findIndex 8 [7,13] 10 = none := by decide
example : findIndex 13 [7,13] (2^80) = some (2^80+1) := by decide
example : findIndex "b" ["a","b","b"] 10 = some 11 ∧
    findIndex "b" ["a","b","b"] 99 = some 100 := by decide
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def old : Spt (Spt Nat) := sptFromAList [(1,sptFromAList [(7,20)])]
private def load : LabLineHOL 8 := .asm (.shareMem .load8 3 (.addr 2 5)) [0,0] 2
private def store : LabLineHOL 8 := .asm (.shareMem .store8 4 (.addr 2 (-1))) [0,0] 2
private def code : LabProgHOL 8 :=
  [⟨0,[]⟩,⟨1,[.label 1 7 0,load,.asm (.cbw 1 2) [0,0] 2,
    .labAsm (.jump (.lab 1 7)) 99 [0,0] 2,.label 1 7 0]⟩,
    ⟨2,[store,.asm (.asmi (.inst .skip)) [0,0] 2]⟩,⟨0,[]⟩]
example (p : Nat) : ∃ index, ∀ nextOffset,
    findIndex (p+posVal 0 0 code)
      ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc) nextOffset =
        some (index+nextOffset) := by
  obtain ⟨index,_,_,hsearch,_,_⟩ := shmemInfo_sharedIndex code p 18
    (cfg (width := 8) 1 [0,0]) old [] (by cbv)
    (by simp [encOk,offsetMonotonic,cfg]) (by cbv)
    0 .load8 3 (.addr 2 5) [0,0] 2 (by cbv)
  have h := findIndexShift _ _ 0 index hsearch
  exact ⟨index,by simpa only [Nat.sub_zero] using h.2⟩
end Flapjack.Test.MiscFindIndexShiftParity
