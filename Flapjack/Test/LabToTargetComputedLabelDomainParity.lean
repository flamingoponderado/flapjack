import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelDomain
namespace Flapjack.Test.LabToTargetComputedLabelDomainParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabProps.LabelSets
private def initial : Spt (Spt Nat) := sptInsert 99 (sptFromAList [(0,777),(5,2^90)]) .ln
private def code : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,.label 9 0 4,
       .labAsm .halt 99 [] 2,.label 88 2 1]⟩,⟨8,[]⟩,⟨9,[.label 888 5 2]⟩]
example : computeLabelsAlt 6 code initial =
    sptInsert 9 (sptFromAList [(0,16),(5,18)])
      (sptInsert 8 (sptFromAList [(0,16)])
        (sptInsert 7 (sptFromAList [(0,6),(2,16),(2,6)]) initial)) := rfl
example : labsDomain (computeLabelsAlt 6 code initial) = getCodeLabels code ∪ labsDomain initial := by
  apply labsDomain_computeLabelsAlt
  constructor
  · decide +kernel
  · apply Set.disjoint_left.mpr
    intro n hn hm
    simp [code] at hm
    simp [initial,sptDomainInsert,sptDomain] at hn
    change n = 99 at hn
    rcases hm with rfl | rfl | rfl <;> contradiction
example : labLookup 99 5 (computeLabelsAlt 6 code initial) = some (2^90) ∧
    labLookup 7 2 (computeLabelsAlt 6 code initial) = some 16 ∧
    labLookup 8 0 (computeLabelsAlt 6 code initial) = some 16 := by
  decide +kernel
private def duplicate : List (Section (LabLineHOL 8)) := [⟨7,[.label 7 4 1]⟩,⟨7,[]⟩]
example : ¬ (duplicate.map (fun s => s.sectionId)).Nodup ∧
    labLookup 7 4 (computeLabelsAlt 0 duplicate .ln) = none ∧
    (7,4) ∈ getCodeLabels duplicate := by
  simp [duplicate,computeLabelsAlt,sectionLabels,labLookup,sptLookup,sptInsert,
    sptFromAList,getCodeLabels,secGetCodeLabels,lineGetCodeLabels]
private def overlapping : Spt (Spt Nat) := sptInsert 7 (sptFromAList [(8,99)]) .ln
example : labLookup 7 8 overlapping = some 99 ∧
    labLookup 7 8 (computeLabelsAlt 0 ([⟨7,[]⟩] : List (Section (LabLineHOL 8))) overlapping) = none := by
  decide +kernel
example : computeLabelsAlt (width := 1) 17 [] initial = initial := rfl
example : computeLabelsAlt (width := 80) (2^80)
    [⟨9,[.label 999 0 1,.label 888 5 2]⟩] initial =
    sptInsert 9 (sptFromAList [(0,2^80),(5,2^80+3)]) initial := rfl
example {width : Nat} [NeZero width] (pos : Nat) (code : List (Section (LabLineHOL width)))
    (labs : Spt (Spt Nat)) :
    (code.map (fun s => s.sectionId)).Nodup ∧
    Disjoint (sptDomain labs) {n | n ∈ code.map (fun s => s.sectionId)} →
    labsDomain (computeLabelsAlt pos code labs) = getCodeLabels code ∪ labsDomain labs :=
  labsDomain_computeLabelsAlt pos code labs

def runChecks : IO Bool := do
  IO.println "PASS full computed label domain: original guards, full nested map, guard counterexamples, widths1/8/80"
  pure true
end Flapjack.Test.LabToTargetComputedLabelDomainParity
