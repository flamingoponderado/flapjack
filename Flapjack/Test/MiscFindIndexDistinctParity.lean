import Flapjack.Misc.FindIndex.Distinct
import Flapjack.Compiler.Backend.LabToTarget.ShmemDistinct
namespace Flapjack.Test.MiscFindIndexDistinctParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {α : Type} [DecidableEq α] [Nonempty α]
    (values : List α) : values.Nodup → ∀ (target : α) (offset index : Nat),
    findIndex target values offset = some index ↔
    ∃ j, index = offset+j ∧ j < values.length ∧ target = holEl j values :=
  findIndex_allDistinct_elEq values
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
example : findIndex (7 : Nat) [7,13] 0 = some 0 := by cbv
example : findIndex (13 : Nat) [7,13] 0 = some 1 := by cbv
example : findIndex (13 : Nat) [7,13] 10 = some 11 := by cbv
example : findIndex (13 : Nat) [7,13] 1208925819614629174706176 = some 1208925819614629174706177 := by cbv
example : findIndex (8 : Nat) [7,13] 10 = none := by cbv
example : findIndex (7 : Nat) [7,7] 0 ≠ some 1 ∧ ¬([7,7] : List Nat).Nodup ∧ holEl 1 ([7,7] : List Nat) = 7 := by
  simp [findIndex,holEl,holHd,List.Nodup,List.pairwise_cons]
example : findIndex (7 : Nat) [] 1000 = none := by cbv
example : ((getShmemInfo code 7 [] []).2.map ShmemInfoNum.entryPc) = [7,13] ∧
    findIndex (13 : Nat) ((getShmemInfo code 7 [] []).2.map ShmemInfoNum.entryPc) 10 = some 11 := by cbv
example (p offset index : Nat) :
    findIndex (posVal 0 p code) ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc) offset = some index ↔
    ∃ j, index = offset+j ∧ j < ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc).length ∧
      posVal 0 p code = holEl j ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc) := by
  apply findIndex_allDistinct_elEq
  exact getShmemInfo_entryDistinct code (cfg (width := 8) 1 [0,0]) old [] 18 p
    ⟨by cbv,by simp [encOk,offsetMonotonic,cfg],by cbv⟩
end Flapjack.Test.MiscFindIndexDistinctParity
