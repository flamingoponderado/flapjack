import Flapjack.Compiler.Backend.LabToTarget.GoodCode

namespace Flapjack.Test.LabToTargetGoodCodeParity
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
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.BackendProps
private def cache : Spt (Spt Bool) := sptInsert 3 (sptInsert 4 false .ln) .ln
private def code : LabProgHOL 8 := [⟨1,[.label 1 1 5]⟩]
private def refs : LabProgHOL 8 :=
  [⟨1,[.labAsm (.jump (.lab 3 4)) 99 [] 0,.label 1 1 0]⟩]
example : goodCode cfg (.ln : Spt (Spt Bool)) [] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : goodCode cfg (.ln : Spt (Spt Bool)) code := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, code, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.label 2 1 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.label 1 0 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.label 1 1 0]⟩,⟨1,[.label 1 2 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.label 1 1 0,.label 1 1 7]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.label 1 1 0,.asm (.asmi (.inst .skip)) [] 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) refs := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, refs, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : goodCode cfg cache refs := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, refs, cache, sptInsert, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (sptInsert 1 (.ln : Spt Bool) .ln) code := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, code, sptInsert, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.labAsm (.jump (.lab 3 0)) 99 [] 0,.label 1 1 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.labAsm (.call (.lab 3 4)) 99 [] 0,.label 1 1 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.asm (.asmi (.inst .skip)) [255] 37,.label 1 1 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

example : ¬ goodCode cfg (.ln : Spt (Spt Bool)) [⟨1,[.asm (.asmi (.inst (.const 40 1))) [] 0,.label 1 1 0]⟩] := by
  simp [goodCode, Set.disjoint_right, sptDomain, isLabelHOL, secEndsWithLabelNative, secLabelsOk, secLabelOk, extractLabels, restrictNonzero, getLabels, secGetLabels, lineGetLabels, labsOf, getCodeLabels, secGetCodeLabels, lineGetCodeLabels, labsDomain, labLookup, sptLookup, allEncOkPreHOL, secOkPreHOL, lineOkPreHOL, Set.subset_def, asmOkExact, asmInstOkExact, asmRegOkExact, cbwToAsmHOL, cfg]

-- Independent source value carrier and all seven original conjuncts remain quantified.
example {width : Nat} [NeZero width] {β : Type} (c : AsmConfigExact width)
    (labels : Spt (Spt β)) (xs : LabProgHOL width) :
    goodCode c labels xs ↔
      (∀ sec ∈ xs, secEndsWithLabelNative sec) ∧
      (∀ sec ∈ xs, secLabelsOk sec) ∧
      (xs.map Section.sectionId).Nodup ∧
      (∀ sec ∈ xs, (extractLabels sec.lines).Nodup) ∧
      Disjoint (α := Set Nat) (Set.ofPred (sptDomain labels)) {n | n ∈ xs.map Section.sectionId} ∧
      restrictNonzero (getLabels xs) ⊆ getCodeLabels xs ∪ labsDomain labels ∧
      allEncOkPreHOL c xs := Iff.rfl

def runChecks : IO Bool := do
  IO.println "PASS full original seven-conjunct good_code (15 observations, independent generic carrier consumer)"
  return true
end Flapjack.Test.LabToTargetGoodCodeParity
