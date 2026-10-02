import Flapjack.Compiler.Backend.LabToTarget.ValidityNop
namespace Flapjack.Test.LabToTargetValidityNopParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack
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
example : lineOk cfg labs ffis 4 (.label 1 5 0) ∧ lineEncWithNop cfg.encode labs ffis 4 (.label 1 5 0) := by
  have h : lineOk cfg labs ffis 4 (.label 1 5 0) := by
    simp [lineOk]
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) ∧ lineEncWithNop cfg.encode labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) := by
  have h : lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) := by
    simp [lineOk,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.labAsm .halt 99 [236,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm .halt 99 [236,99] 2) := by
  have h : lineOk cfg labs ffis 4 (.labAsm .halt 99 [236,99] 2) := by
    simp [lineOk,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.labAsm .install 99 [220,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm .install 99 [220,99] 2) := by
  have h : lineOk cfg labs ffis 4 (.labAsm .install 99 [220,99] 2) := by
    simp [lineOk,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.labAsm (.callFFI (.implode [98])) 99 [188,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.callFFI (.implode [98])) 99 [188,99] 2) := by
  have h : lineOk cfg labs ffis 4 (.labAsm (.callFFI (.implode [98])) 99 [188,99] 2) := by
    simp [lineOk,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.labAsm (.jump (.lab 1 5)) 99 [16,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.jump (.lab 1 5)) 99 [16,99] 2) := by
  have h : lineOk cfg labs ffis 4 (.labAsm (.jump (.lab 1 5)) 99 [16,99] 2) := by
    simp [lineOk,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 99 [16,88] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 99 [16,88] 2) := by
  have h : lineOk cfg labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 99 [16,88] 2) := by
    simp [lineOk,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : lineOk cfg labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 99 [16,77] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 99 [16,77] 2) := by
  have h : lineOk cfg labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 99 [16,77] 2) := by
    simp [lineOk,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
  exact ⟨h, lineOk_lineEncWithNop cfg labs ffis 4 _ h⟩
example : linesOk cfg labs ffis 4 [.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 5)) 99 [14,99] 2] ∧ linesEncWithNop cfg.encode labs ffis 4 [.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 5)) 99 [14,99] 2] := by
  have h : linesOk cfg labs ffis 4 [.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 5)) 99 [14,99] 2] := by
    simp [linesOk,lineOk,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop,lineLength] <;> decide +kernel
  exact ⟨h, linesOk_linesEncWithNop cfg labs ffis 4 _ h⟩

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineOk c labs ffis pos line → lineEncWithNop c.encode labs ffis pos line := lineOk_lineEncWithNop c labs ffis pos line

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesOk c labs ffis pos lines → linesEncWithNop c.encode labs ffis pos lines := linesOk_linesEncWithNop c labs ffis pos lines

def runChecks : IO Bool := do
  IO.println "PASS full validity-to-NOP implications (9 original observations, 9 actual premise instances, 2 full consumers)"
  pure true
end Flapjack.Test.LabToTargetValidityNopParity
