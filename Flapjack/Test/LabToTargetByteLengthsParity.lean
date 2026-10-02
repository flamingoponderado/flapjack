import Flapjack.Compiler.Backend.LabToTarget.ByteLengths

namespace Flapjack.Test.LabToTargetByteLengthsParity
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
private def ls : List (LabLineHOL 8) :=
  [.label 1 5 0, .asm (.asmi (.inst .skip)) [0,0] 2, .labAsm .halt 99 [238,99] 2]
private theorem lines_valid : linesOk cfg labs ffis 0 ls := by
  simp only [ls, linesOk, lineOk, encWithNop]
  decide +kernel
private def oddCfg : AsmConfigExact 8 := {cfg with encode := fun _ => [0]}
private def oddCode : LabProgHOL 8 := [⟨1,[.asm (.asmi (.inst .skip)) [0] 1]⟩]
example : progToBytes (code ++ code) = progToBytes code ++ progToBytes code := progToBytes_append code code
example : (lineBytes (.label 1 5 0 : LabLineHOL 8)).length = Flapjack.Compiler.Backend.LabProps.lineLength (.label 1 5 0 : LabLineHOL 8) :=
  lineOk_lineByteLength cfg labs ffis 0 _ (by simp [lineOk])
example : (lineBytes (.asm (.asmi (.inst .skip)) [0,0] 2 : LabLineHOL 8)).length = 2 := rfl
example : (lineBytes (.labAsm .halt 99 [238,99] 2 : LabLineHOL 8)).length = 2 := rfl
example : (ls.map lineBytes).map List.length = ls.map Flapjack.Compiler.Backend.LabProps.lineLength :=
  linesOk_mapLineByteLength ls cfg labs ffis 0 lines_valid
example : (progToBytes code).length % 2 = 0 :=
  allEncOk_progToBytes_even code cfg labs ffis 0 ⟨rfl,code_valid⟩
example : ¬ lineOk cfg labs ffis 0 (.label 1 5 1) := by simp [lineOk]
-- These actual cases show that the original EVEN-start guard cannot be omitted.
example : allEncOk oddCfg labs ffis 1 oddCode := by
  simp only [oddCode, allEncOk, lineOk, encWithNop]
  decide +kernel
example : (progToBytes oddCode).length % 2 ≠ 0 := by
  simp [progToBytes, oddCode, lineBytes]
example : ¬ allEncOk oddCfg labs ffis 0 oddCode := by
  simp only [oddCode, allEncOk, lineOk, encWithNop]
  decide +kernel
example {width : Nat} [NeZero width] (c1 c2 : LabProgHOL width) :
    progToBytes (c1 ++ c2) = progToBytes c1 ++ progToBytes c2 := progToBytes_append c1 c2
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labels : Spt (Spt Nat))
    (names : List HolFfiName) (n : Nat) (line : LabLineHOL width) (h : lineOk c labels names n line) :
    (lineBytes line).length = Flapjack.Compiler.Backend.LabProps.lineLength line := lineOk_lineByteLength c labels names n line h
example {width : Nat} [NeZero width] (ls : List (LabLineHOL width)) (c : AsmConfigExact width)
    (labels : Spt (Spt Nat)) (names : List HolFfiName) (n : Nat) (h : linesOk c labels names n ls) :
    (ls.map lineBytes).map List.length = ls.map Flapjack.Compiler.Backend.LabProps.lineLength := linesOk_mapLineByteLength ls c labels names n h
example {width : Nat} [NeZero width] (xs : LabProgHOL width) (c : AsmConfigExact width)
    (labels : Spt (Spt Nat)) (names : List HolFfiName) (pos : Nat)
    (h : pos % 2 = 0 ∧ allEncOk c labels names pos xs) : (progToBytes xs).length % 2 = 0 :=
  allEncOk_progToBytes_even xs c labels names pos h

def runChecks : IO Bool := do
  IO.println "PASS original physical byte lengths and full even-output law (10 observations, 4 generic consumers, 2 validity instances)"
  return true
end Flapjack.Test.LabToTargetByteLengthsParity
