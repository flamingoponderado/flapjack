import Flapjack.Compiler.Backend.LabToTarget.LabelLookupEvenness
namespace Flapjack.Test.LabToTargetLabelLookupEvennessParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
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

private def lines : List (LabLineHOL 8) := [.label 7 2 0,.asm (.asmi (.inst .skip)) [0,0] 2,
  .labAsm (.jump (.lab 1 5)) 99 [14,99] 2,.label 7 2 0,.label 9 0 0]
private def aux : List (Nat × Nat) := [(0,22),(2,40),(2,3),(9,60)]
private def code : List (Section (LabLineHOL 8)) := [⟨7,lines⟩,⟨8,[]⟩]
private def initial : Spt (Spt Nat) := sptInsert 99 (sptFromAList [(5,2^80),(6,3)]) .ln
example : sectionLabels 4 lines aux = (8,[(2,8),(2,4),(0,22),(2,40),(2,3),(9,60)]) := rfl
example : linesOk cfg labs ffis 4 lines := by
  simp [lines,linesOk,lineOk,lineLength,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : sptAListLookup 2 aux = some 40 ∧ sptAListLookup 2 (sectionLabels 4 lines aux).2 = some 8 := ⟨rfl,rfl⟩
example : ∀ k x,sptAListLookup k aux = some x → x % 2 = 0 := by
  intro k x hx
  by_cases h0 : k = 0
  · simp [aux,sptAListLookup,h0] at hx; subst x; decide +kernel
  · by_cases h2 : k = 2
    · simp [aux,sptAListLookup,h2] at hx; subst x; decide +kernel
    · by_cases h9 : k = 9
      · simp [aux,sptAListLookup,h9] at hx; subst x; decide +kernel
      · simp [aux,sptAListLookup,h0,h2,h9] at hx
example : allEncOk cfg labs ffis 4 code ∧ secLength lines 4 = 8 := by
  simp [code,lines,allEncOk,lineOk,lineLength,secLength,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop] <;> decide +kernel
example : computeLabelsAlt 4 code initial = sptInsert 8 (sptFromAList [(0,8)])
    (sptInsert 7 (sptFromAList [(0,4),(2,8),(2,4)]) initial) := rfl
example : labLookup 7 2 (computeLabelsAlt 4 code initial) = some 8 ∧
    labLookup 99 5 (computeLabelsAlt 4 code initial) = some (2^80) ∧
    labLookup 99 6 (computeLabelsAlt 4 code initial) = some 3 := by decide +kernel
example : allEncOk cfg labs ffis 4 ([⟨7,lines⟩,⟨7,[.label 99 4 0]⟩] : List (Section (LabLineHOL 8))) ∧
    labLookup 7 4 (computeLabelsAlt 4 ([⟨7,lines⟩,⟨7,[.label 99 4 0]⟩] : List (Section (LabLineHOL 8))) initial) = some 8 ∧
    labLookup 7 2 (computeLabelsAlt 4 ([⟨7,lines⟩,⟨7,[.label 99 4 0]⟩] : List (Section (LabLineHOL 8))) initial) = none := by
  simp [lines,allEncOk,lineOk,lineLength,getLabel,labLookup,labs,sptLookup,sptInsert,encWithNop,computeLabelsAlt,sectionLabels,sptFromAList] <;> decide +kernel
private def cfgOne : AsmConfigExact 8 := { cfg with encode := fun _ => [0] }
example : allEncOk cfgOne labs ffis 3 ([⟨7,[.asm (.asmi (.inst .skip)) [0] 1]⟩] : List (Section (LabLineHOL 8))) ∧
    labLookup 7 0 (computeLabelsAlt 3 ([⟨7,[.asm (.asmi (.inst .skip)) [0] 1]⟩] : List (Section (LabLineHOL 8))) .ln) = some 3 := by
  simp [allEncOk,lineOk,lineLength,encWithNop,labLookup,computeLabelsAlt,sectionLabels,sptLookup,sptInsert,sptFromAList,cfgOne] <;> decide +kernel
example : ¬allEncOk cfg labs ffis 4 ([⟨7,[.label 99 2 1]⟩] : List (Section (LabLineHOL 8))) ∧
    labLookup 7 2 (computeLabelsAlt 4 ([⟨7,[.label 99 2 1]⟩] : List (Section (LabLineHOL 8))) .ln) = some 5 := by
  simp [allEncOk,lineOk,labLookup,computeLabelsAlt,sectionLabels,sptLookup,sptInsert,sptFromAList]
example : linesOk cfg labs ffis 4 [] ∧ sptAListLookup 2 (sectionLabels (width := 8) 4 [] [(2,3)]).2 = some 3 := by
  simp [linesOk,sectionLabels,sptAListLookup]
example : computeLabelsAlt (width := 1) 17 [] initial = initial := rfl
example : labLookup 7 5 (computeLabelsAlt (width := 80) (2^80) [⟨7,[.label 99 5 0]⟩] initial) = some (2^80) := by
  decide +kernel
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (lines : List (LabLineHOL width)) (acc : List (Nat×Nat)) (k x : Nat) :
    linesOk c labs ffis pos lines ∧ (∀ k x,sptAListLookup k acc = some x → x%2=0) ∧
    sptAListLookup k (sectionLabels pos lines acc).2 = some x → x%2=0 :=
  linesOk_sectionLabels_lookup_even c labs ffis pos lines acc k x
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (code : List (Section (LabLineHOL width))) (k1 k2 : Nat)
    (acc : Spt (Spt Nat)) (x : Nat) :
    allEncOk c labs ffis pos code ∧ labLookup k1 k2 (computeLabelsAlt pos code acc) = some x ∧
    (∀ x,labLookup k1 k2 acc = some x → x%2=0) ∧ pos%2=0 → x%2=0 :=
  allEncOk_computeLabels_lookup_even c labs ffis pos code k1 k2 acc x

example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos k : Nat) (lines : List (LabLineHOL width))
    (rest : List (Section (LabLineHOL width))) :
    allEncOk c labs ffis pos (⟨k,lines⟩::rest) → allEncOk c labs ffis pos [⟨k,lines⟩] ∧
    allEncOk c labs ffis (pos + secLength lines 0) rest := allEncOk_split c labs ffis pos k lines rest
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (k : Nat) (lines : List (LabLineHOL width)) (pos : Nat) :
    allEncOk c labs ffis pos [⟨k,lines⟩] → (secLength lines pos)%2=0 := allEncOk_even c labs ffis k lines pos

def runChecks : IO Bool := do
  IO.println "PASS full computed-label lookup evenness: original guards, full tuple/map, duplicate keys/sections and widths1/8/80"
  pure true
end Flapjack.Test.LabToTargetLabelLookupEvennessParity
