import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity

namespace Flapjack.Test.LabToTargetEncodingValidityParity
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

example : labLookup 1 5 (sptInsert 1 (sptInsert 5 true .ln) .ln) = some true := by decide +kernel
example : labLookup 2 5 labs = none := by decide +kernel
example : labLookup 1 6 labs = none := by decide +kernel
example : lineOk cfg labs ffis 4 (.label 1 5 0) := by
  simp only [lineOk]
  decide +kernel
example : ¬ lineOk cfg labs ffis 3 (.label 1 5 0) := by
  simp only [lineOk]
  decide +kernel
example : ¬ lineOk cfg labs ffis 4 (.label 1 5 2) := by
  simp only [lineOk]
  decide +kernel
example : lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : ¬ lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [0,0] 3) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : ¬ lineOk cfg labs ffis 4 (.asm (.asmi (.inst .skip)) [1,1] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : ¬ lineOk cfg labs ffis 4 (.asm (.asmi (.inst (.const 40 1))) [10,11] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : lineOk cfg labs ffis 4 (.asm (.cbw 1 2) [10,11] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : lineOk cfg labs ffis 4 (.labAsm .halt 99 [236,99] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : lineOk cfg labs ffis 4 (.labAsm .install 99 [220,99] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : lineOk cfg labs ffis 4 (.labAsm (.callFFI (.implode [98])) 99 [188,99] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : lineOk cfg labs ffis 4 (.labAsm (.callFFI (.implode [122])) 99 [204,99] 2) := by
  simp only [lineOk, encWithNop]
  decide +kernel
example : ¬ lineOk cfg labs ffis 4 (.labAsm (.call (.lab 1 5)) 0 [16,99] 2) := by
  simp only [lineOk]
  decide +kernel
example : lineOk cfg labs ffis 4 (.labAsm (.jump (.lab 1 5)) 99 [16,99] 2) := by
  simp [lineOk, getLabel, labLookup, labs, sptLookup, sptInsert, encWithNop] <;> decide +kernel

example : lineOk cfg labs ffis 4 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 1 5)) 99 [16,88] 2) := by
  simp [lineOk, getLabel, labLookup, labs, sptLookup, sptInsert, encWithNop] <;> decide +kernel

example : lineOk cfg labs ffis 4 (.labAsm (.locValue 2 (.lab 1 5)) 99 [16,77] 2) := by
  simp [lineOk, getLabel, labLookup, labs, sptLookup, sptInsert, encWithNop] <;> decide +kernel

example : ¬ lineOk cfg labs ffis 4 (.labAsm (.jump (.lab 1 6)) 0 [0,99] 2) := by
  simp [lineOk, getLabel, labLookup, labs, sptLookup, sptInsert]

example : allEncOk cfg labs ffis 3 ([] : LabProgHOL 8) := by simp [allEncOk]
example : allEncOk cfg labs ffis 4 [⟨1, []⟩] := by simp [allEncOk]
example : ¬ allEncOk cfg labs ffis 3 [⟨1, []⟩] := by simp [allEncOk]
private theorem code_valid : allEncOk cfg labs ffis 0 code := by
  simp only [code, allEncOk, lineOk, encWithNop]
  decide +kernel
example : (progToBytes code).length = 4 := by simp [progToBytes, code, lineBytes]
example : posVal 0 0 code = 0 := by decide +kernel
example : posVal 2 17 code = 21 := by decide +kernel
-- Full consumers have actual premise instances, not assumed success callbacks.
example : posVal 0 0 code = 0 := posVal_zero code cfg labs ffis 0 code_valid
example : posVal 2 17 code ≤ 17 + (progToBytes code).length :=
  posVal_bound 2 17 code cfg labs ffis 0 code_valid
example : ∀ sec ∈ code, secLabelZero sec :=
  allEncOk_implies_secLabelZero cfg labs ffis 0 code code_valid
-- Arbitrary native config/instructions and independent offsets remain quantified.
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labels : Spt (Spt Nat))
    (names : List HolFfiName) (xs : LabProgHOL width) (i pos n : Nat)
    (h : allEncOk c labels names n xs) :
    posVal i pos xs ≤ pos + (progToBytes xs).length := posVal_bound i pos xs c labels names n h
example {α : Type} (l1 l2 : Nat) (xs : Spt (Spt α)) :
    labLookup l1 l2 xs = (sptLookup l1 xs).bind (sptLookup l2) := by
  cases h : sptLookup l1 xs <;> simp [labLookup, h]
example : findPos (.lab 1 5) labs = 20 :=
  labLookup_implies_findPos 1 5 labs 20 (by decide +kernel)

example : allEncOk cfg labs ffis 0 code ↔
    allEncOk cfg labs ffis 4 [⟨2, []⟩] ∧ 4 % 2 = 0 ∧
    linesOk cfg labs ffis 0 [.label 1 5 0, .asm (.asmi (.inst .skip)) [0,0] 2,
      .labAsm .halt 99 [238,99] 2] := by
  simpa [code, Flapjack.Compiler.Backend.LabProps.lineLength] using
    allEncOk_cons cfg labs ffis
      [.label 1 5 0, .asm (.asmi (.inst .skip)) [0,0] 2, .labAsm .halt 99 [238,99] 2]
      0 1 [⟨2, []⟩]

def runChecks : IO Bool := do
  IO.println "PASS original full native encoding validity (28 observations, 7 full generic/consumer checks)"
  return true
end Flapjack.Test.LabToTargetEncodingValidityParity
