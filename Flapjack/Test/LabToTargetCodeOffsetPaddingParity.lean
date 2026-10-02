import Flapjack.Compiler.Backend.LabToTarget.CodeOffsetPadding
namespace Flapjack.Test.LabToTargetCodeOffsetPaddingParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def code : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 0,.labAsm .halt 240 [] 3,.label 1 3 1]⟩,
   ⟨8,[.label 1 4 0,.labAsm (.call (.lab 3 4)) 6 [] 3,.label 1 5 1]⟩,⟨9,[]⟩]
private def zeroCode : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 0,.labAsm .halt 240 [] 2,.label 1 3 0]⟩,
   ⟨8,[.label 1 4 0,.labAsm (.jump (.lab 3 4)) 8 [] 2,.label 1 5 0]⟩,⟨9,[]⟩]
private theorem guards :
    (([0] : List (BitVec 8)).length ≠ 1 → ∀ sec ∈ code,secLabelZero sec) ∧
    (∀ sec ∈ code,secLabelOne sec) ∧ (∀ sec ∈ code,secLabelPrefixZero sec) ∧
    allLabLenPosOk 0 code ∧ offsetOk labs [] 0 code := by
  simp [code,secLabelOne,secLabelPrefixZero,labelPrefixZero,
    labelOne,isLabelHOL,lineLen,allLabLenPosOk,labLenPosOk,lineLabLenPosOk,
    secLength,offsetOk,linesOffsetOk,lineOffsetOk,getJumpOffset,findPos,getLabel,
    lookupAny,labs,sptLookup,sptInsert,ffiOffset]
  all_goals decide +kernel
example := guards
example : padCode [0] code =
    [⟨7,[.label 1 2 0,.labAsm .halt 240 [0,0,0,0] 4,.label 1 3 0]⟩,
     ⟨8,[.label 1 4 0,.labAsm (.call (.lab 3 4)) 6 [0,0,0,0] 4,.label 1 5 0]⟩,⟨9,[]⟩] := rfl
example : offsetOk labs [] 0 (padCode [0] code) := offsetOk_padCode [0] labs [] 0 code guards
private theorem zeroGuards (nop : List (BitVec 8)) :
    (nop.length ≠ 1 → ∀ sec ∈ zeroCode,secLabelZero sec) ∧
    (∀ sec ∈ zeroCode,secLabelOne sec) ∧ (∀ sec ∈ zeroCode,secLabelPrefixZero sec) ∧
    allLabLenPosOk 0 zeroCode ∧ offsetOk labs [] 0 zeroCode := by
  simp [zeroCode,secLabelZero,secLabelOne,secLabelPrefixZero,labelPrefixZero,
    labelZero,labelOne,isLabelHOL,lineLen,allLabLenPosOk,labLenPosOk,lineLabLenPosOk,
    secLength,offsetOk,linesOffsetOk,lineOffsetOk,getJumpOffset,findPos,getLabel,
    lookupAny,labs,sptLookup,sptInsert,ffiOffset]
  all_goals decide +kernel
example : padCode [] zeroCode = zeroCode ∧ offsetOk labs [] 0 (padCode [] zeroCode) :=
  ⟨rfl,offsetOk_padCode [] labs [] 0 zeroCode (zeroGuards [])⟩
example : offsetOk labs [] 0 (padCode [7,8] zeroCode) := offsetOk_padCode [7,8] labs [] 0 zeroCode (zeroGuards [7,8])
example : ¬offsetOk (width := 8) .ln [] 1 (padCode [0] [⟨7,[.label 1 2 1,.labAsm .halt 238 [] 0]⟩]) := by
  simp [offsetOk,linesOffsetOk,lineOffsetOk,padCode,padSection,addNop]
  decide +kernel
example : ¬offsetOk (width := 8) .ln [] 0 (padCode [0] [⟨7,[.labAsm .halt 99 [] 2]⟩]) := by
  simp [offsetOk,linesOffsetOk,lineOffsetOk,padCode,padSection]
  decide +kernel
example : offsetOk (width := 1) .ln [] 17 (padCode [0] []) := offsetOk_padCode [0] .ln [] 17 [] (by simp [allLabLenPosOk,offsetOk])
example {width : Nat} [NeZero width] (nop : List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (code : List (Section (LabLineHOL width))) :
    (nop.length ≠ 1 → ∀ sec ∈ code,secLabelZero sec) ∧
    (∀ sec ∈ code,secLabelOne sec) ∧ (∀ sec ∈ code,secLabelPrefixZero sec) ∧
    allLabLenPosOk pos code ∧ offsetOk labs ffis pos code → offsetOk labs ffis pos (padCode nop code) :=
  offsetOk_padCode nop labs ffis pos code

def runChecks : IO Bool := do
  IO.println "PASS full code padding offset preservation: original five guards, actual section positions, empty/multibyte NOPs and guarded counterexamples"
  pure true
end Flapjack.Test.LabToTargetCodeOffsetPaddingParity
