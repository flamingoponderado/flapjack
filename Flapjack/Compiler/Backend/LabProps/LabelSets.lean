import Flapjack.Compiler.Backend.LabSem.Navigation
import Mathlib.Data.Set.Basic

/-! Literal original LabProps label extraction and label-set section.
BIGUNION of IMAGE over a list set is written in its membership form:
there exists a listed element whose label set contains the queried pair.
The source Word/Asm carriers remain at an arbitrary positive word dimension. -/
namespace Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "extract_labels_def"
  (words_as_type_indexed_bitvec)]
def extractLabels {width : Nat} [NeZero width] : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → List (Nat × Nat)
  | [] => []
  | .label l1 l2 _ :: xs => (l1,l2) :: extractLabels xs
  | _ :: xs => extractLabels xs

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "extract_labels_append"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_append {width : Nat} [NeZero width] (A B : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    extractLabels (A ++ B) = extractLabels A ++ extractLabels B := by
  induction A with
  | nil => rfl
  | cons line xs ih => cases line <;> simp [extractLabels, ih]

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "labs_of_def"
  (words_as_type_indexed_bitvec)]
def labsOf {width : Nat} [NeZero width]
    (instruction : AsmWithLab HolCmp (HolRegImm width) MlString) : Set (Nat × Nat) :=
  match instruction with
  | .locValue _ (.lab n1 n2) | .jump (.lab n1 n2)
  | .jumpCmp _ _ _ (.lab n1 n2) => {(n1,n2)}
  | _ => ∅

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_get_labels_def"
  (words_as_type_indexed_bitvec)]
def lineGetLabels {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Set (Nat × Nat) :=
  match line with
  | .labAsm instruction _ _ _ => labsOf instruction
  | _ => ∅

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_get_labels_def"
  (words_as_type_indexed_bitvec)]
def secGetLabels {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Set (Nat × Nat) :=
  {label | ∃ line ∈ sec.lines, label ∈ lineGetLabels line}

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_labels_def"
  (words_as_type_indexed_bitvec)]
def getLabels {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Set (Nat × Nat) :=
  {label | ∃ sec ∈ code, label ∈ secGetLabels sec}

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_labels_cons"
  (words_as_type_indexed_bitvec)]
theorem getLabels_cons {width : Nat} [NeZero width] (x : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (xs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    getLabels (x :: xs) = secGetLabels x ∪ getLabels xs := by
  ext label
  simp [getLabels]

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_get_code_labels_def"
  (words_as_type_indexed_bitvec)]
def lineGetCodeLabels {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Set Nat :=
  match line with
  | .label _ l _ => {l}
  | _ => ∅

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_get_code_labels_def"
  (words_as_type_indexed_bitvec)]
def secGetCodeLabels {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Set (Nat × Nat) :=
  {(sec.sectionId,0)} ∪
    {label | ∃ n2, (∃ line ∈ sec.lines, n2 ∈ lineGetCodeLabels line) ∧
      label = (sec.sectionId,n2)}

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_def"
  (words_as_type_indexed_bitvec)]
def getCodeLabels {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Set (Nat × Nat) :=
  {label | ∃ sec ∈ code, label ∈ secGetCodeLabels sec}

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_nil"
  (words_as_type_indexed_bitvec)]
theorem getCodeLabels_nil {width : Nat} [NeZero width] :
    getCodeLabels ([] : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) = ∅ := by
  ext label
  simp [getCodeLabels]

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_cons"
  (words_as_type_indexed_bitvec)]
theorem getCodeLabels_cons {width : Nat} [NeZero width] (s : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    getCodeLabels (s :: secs) = secGetCodeLabels s ∪ getCodeLabels secs := by
  ext label
  simp [getCodeLabels]

end Flapjack.Compiler.Backend.LabProps.LabelSets
