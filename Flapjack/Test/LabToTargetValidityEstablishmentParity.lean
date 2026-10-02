import Flapjack.Compiler.Backend.LabToTarget.ValidityEstablishment
namespace Flapjack.Test.LabToTargetValidityEstablishmentParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabProps.LabelSets
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
example : lineOkPreHOL cfg (.label 1 5 0) ∧ lineEncWithNop cfg.encode labs ffis 4 (.label 1 5 0) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.label 1 5 0) ∧ lineLabsExist (width := 8) labs (.label 1 5 0) ∧
    lineOkLight cfg (.label 1 5 0) = true ∧ (isLabelHOL (width := 8) (.label 1 5 0) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.label 1 5 0) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) ∧ lineEncWithNop cfg.encode labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) ∧ lineLabsExist (width := 8) labs (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) ∧
    lineOkLight cfg (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) = true ∧ (isLabelHOL (width := 8) (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.labAsm .halt 236 [236,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm .halt 236 [236,99] 2) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.labAsm .halt 236 [236,99] 2) ∧ lineLabsExist (width := 8) labs (.labAsm .halt 236 [236,99] 2) ∧
    lineOkLight cfg (.labAsm .halt 236 [236,99] 2) = true ∧ (isLabelHOL (width := 8) (.labAsm .halt 236 [236,99] 2) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.labAsm .halt 236 [236,99] 2) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.labAsm .install 220 [220,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm .install 220 [220,99] 2) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.labAsm .install 220 [220,99] 2) ∧ lineLabsExist (width := 8) labs (.labAsm .install 220 [220,99] 2) ∧
    lineOkLight cfg (.labAsm .install 220 [220,99] 2) = true ∧ (isLabelHOL (width := 8) (.labAsm .install 220 [220,99] 2) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.labAsm .install 220 [220,99] 2) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) ∧ lineLabsExist (width := 8) labs (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) ∧
    lineOkLight cfg (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) = true ∧ (isLabelHOL (width := 8) (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.labAsm (.callFFI (.implode [98])) 188 [188,99] 2) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) ∧ lineLabsExist (width := 8) labs (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) ∧
    lineOkLight cfg (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) = true ∧ (isLabelHOL (width := 8) (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.labAsm (.jump (.lab 1 5)) 16 [16,99] 2) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) ∧ lineLabsExist (width := 8) labs (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) ∧
    lineOkLight cfg (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) = true ∧ (isLabelHOL (width := 8) (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 16 [16,88] 2) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : lineOkPreHOL cfg (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) ∧ lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) ∧
    lineOffsetOk (width := 8) labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) ∧ lineLabsExist (width := 8) labs (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) ∧
    lineOkLight cfg (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) = true ∧ (isLabelHOL (width := 8) (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) = true → 4 % 2 = 0) ∧ lineOk cfg labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 16 [16,77] 2) := by
  simp [lineOkPreHOL,lineEncWithNop,lineOffsetOk,lineLabsExist,lineOkLight,isLabelHOL,lineOk,getJumpOffset,getLabel,labInst,labsOf,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel

example : ¬ evenLabelsStrong 3 ([⟨1,[]⟩] : List (Section (LabLineHOL 8))) ∧
    ¬ allEncOk cfg labs ffis 3 [⟨1,[]⟩] := by simp [evenLabelsStrong,allEncOk,lineEncWithNop,lineOkLight,lineOk]
example : lineEncWithNop cfg.encode labs ffis 4 (.labAsm (.call (.lab 1 5)) 16 [0,0] 2) ∧
    lineOkLight cfg (.labAsm (.call (.lab 1 5)) 16 [0,0] 2) = false ∧
    ¬ lineOk cfg labs ffis 4 (.labAsm (.call (.lab 1 5)) 16 [0,0] 2) := by simp [evenLabelsStrong,allEncOk,lineEncWithNop,lineOkLight,lineOk]
private def mixed : List (Section (LabLineHOL 8)) :=
  [⟨1,[.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,
    .labAsm (.jump (.lab 1 5)) 14 [14,99] 2,.label 1 6 0]⟩]
example : allEncWithNop cfg.encode labs ffis 4 mixed ∧ allEncOkPreHOL cfg mixed ∧
    allEncOkLight cfg mixed = true ∧ evenLabelsStrong 4 mixed ∧ allLabsExist labs mixed ∧
    offsetOk labs ffis 4 mixed ∧ allEncOk cfg labs ffis 4 mixed := by
  simp [mixed,allEncWithNop,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL,allEncOkLight,
    secOkLight,lineOkLight,evenLabelsStrong,allLabsExist,secLabsExist,lineLabsExist,
    labsOf,offsetOk,linesOffsetOk,lineOffsetOk,allEncOk,lineOk,lineEncWithNop,
    lineLength,lineLen,getJumpOffset,getLabel,labInst,isLabelHOL,labLookup,labs,
    sptLookup,sptInsert,encWithNop] <;> decide +kernel
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : LabLineHOL width) :
    lineOkPreHOL c line ∧ lineEncWithNop c.encode labs ffis pos line ∧
    lineOffsetOk labs ffis pos line ∧ lineLabsExist labs line ∧
    lineOkLight c line = true ∧ (isLabelHOL line = true → pos % 2 = 0) →
    lineOk c labs ffis pos line := lineOk_pre_light_establishes c labs ffis pos line
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (code : List (Section (LabLineHOL width))) :
    allEncWithNop c.encode labs ffis pos code ∧ allEncOkPreHOL c code ∧
    allEncOkLight c code = true ∧ evenLabelsStrong pos code ∧ allLabsExist labs code ∧
    offsetOk labs ffis pos code → allEncOk c labs ffis pos code := allEncOk_pre_light_establishes c labs ffis pos code

def runChecks : IO Bool := do
  IO.println "PASS full six-guard encoding establishment (11 original observations, 2 full consumers)"
  pure true
end Flapjack.Test.LabToTargetValidityEstablishmentParity
