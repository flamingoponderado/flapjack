import Flapjack.Compiler.Backend.LabToTarget.FetchValidity

namespace Flapjack.Test.LabToTargetFetchValidityParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm Flapjack
open Flapjack.Basis.Pure.MlString
private def encode8 : HolAsm 8 → List (BitVec 8)
  | .inst .skip => [0,0]
  | .jump w => [w,99]
  | .jumpCmp _ _ _ w => [w,88]
  | .loc _ w => [w,77]
  | _ => [10,11]
private def cfg : AsmConfigExact 8 :=
  { isa := .riscv, encode := encode8, bigEndian := false, codeAlignment := 0,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def labs : Spt (Spt Nat) := sptInsert 1 (sptInsert 5 20 .ln) .ln
private def ffis : List HolFfiName := [.extCall (.implode [97]), .extCall (.implode [98])]
private def code : LabProgHOL 8 :=
  [⟨1, [.label 1 5 0, .asm (.asmi (.inst .skip)) [0,0] 2,
    .labAsm .halt 99 [238,99] 2]⟩, ⟨2, []⟩]

private theorem code_valid : allEncOk cfg labs ffis 0 code := by
  simp only [code, allEncOk, lineOk, encWithNop]
  decide +kernel
example : asmFetchAux 0 code = some (.asm (.asmi (.inst .skip)) [0,0] 2) := by simp [asmFetchAux, code, isLabelHOL]
example : asmFetchAux 1 code = some (.labAsm .halt 99 [238,99] 2) := by simp [asmFetchAux, code, isLabelHOL]
example : asmFetchAux 2 code = none := by simp [asmFetchAux, code, isLabelHOL]
example : lineOk cfg labs ffis (posVal 1 0 code) (.labAsm .halt 99 [238,99] 2) :=
  allEncOk_fetch_lineOk cfg labs ffis 1 0 code _ ⟨code_valid, by simp [asmFetchAux, code, isLabelHOL]⟩
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labels : Spt (Spt Nat)) (names : List HolFfiName) (pc n : Nat)
    (xs : LabProgHOL width) (line : LabLineHOL width)
    (h : allEncOk c labels names n xs ∧ asmFetchAux pc xs = some line) :
    lineOk c labels names (posVal pc n xs) line :=
  allEncOk_fetch_lineOk c labels names pc n xs line h

def runChecks : IO Bool := do
  IO.println "PASS original native fetch validity (5 observations, full generic theorem consumer)"
  return true
end Flapjack.Test.LabToTargetFetchValidityParity
