import Flapjack.Compiler.Backend.LabToTarget.Labels

/-!
# Native kernel replays of `lab_to_target_labels_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_labels_probeScript.sml`, which `EVAL`s the
original `lab_to_target` label-computation definitions
(`section_labels_def`, `compute_labels_alt_def`) on concrete `labLang$line`,
`labLang$sec` and `num_map` values.

The `Line`/`Section` carriers are instantiated at HOL's actual carriers
(`HolAsm`, `HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm`, `MlString`) at the
positive width `8`, with native instruction/word payloads; the
label-computation definitions never inspect those payloads, but the carriers
match the source type.  Every captured row is replayed below as a
kernel-checked `rfl` example and as a `runChecks` runtime comparison.
-/

namespace Flapjack.Test.LabToTargetLabelsParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack

private abbrev L := Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
  (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)
private abbrev S := Section L

private def label0 : L := .label 0 0 0
private def asm1 : L := .asm (.asmi (.inst .skip)) [1] 1
private def label1 : L := .label 0 1 2
private def label2 : L := .label 0 2 4
private def asm2 : L := .asm (.asmi (.inst .skip)) [1, 2] 2
private def labasm3 : L := .labAsm (.jump (.lab 0 0)) (BitVec.ofNat 8 0) [3] 3

private def lines : List L := [label0, asm1, label1, label2, asm2, labasm3]
private def sec1 : S := { sectionId := 1, lines := [label0, asm1, label1] }
private def sec2 : S := { sectionId := 2, lines := [labasm3, label2] }

-- SectionLabelsEmpty
example : sectionLabels 5 ([] : List L) [] = (5, []) := rfl
-- SectionLabelsEmptyLabs
example : sectionLabels 5 ([] : List L) [(9, 9)] = (5, [(9, 9)]) := rfl
-- SectionLabelsConcrete
example : sectionLabels 10 lines [] = (22, [(2, 17), (1, 13)]) := rfl
-- SectionLabelsConcreteLabs
example : sectionLabels 10 lines [(7, 7)] = (22, [(2, 17), (1, 13), (7, 7)]) := rfl
-- ComputeLabelsAltEmpty
example : computeLabelsAlt 5 ([] : List S) (.ln : Spt (Spt Nat)) = .ln := rfl
-- ComputeLabelsAltConcrete
example : computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)) =
    sptInsert 2 (sptFromAList [(0, 13), (2, 20)])
      (sptInsert 1 (sptFromAList [(0, 10), (1, 13)]) .ln) := rfl
-- ComputeLookupSection1
example : sptLookup 1 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat))) =
    some (sptFromAList [(0, 10), (1, 13)]) := by decide +kernel
-- ComputeLookupSection2
example : sptLookup 2 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat))) =
    some (sptFromAList [(0, 13), (2, 20)]) := by decide +kernel
-- ComputeLookupSection3Absent
example : sptLookup 3 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat))) =
    none := by decide +kernel
-- ComputeLookupSection1Start
example :
    (sptLookup 1 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 0) = some 10 := by decide +kernel
-- ComputeLookupSection1Label1
example :
    (sptLookup 1 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 1) = some 13 := by decide +kernel
-- ComputeLookupSection2Start
example :
    (sptLookup 2 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 0) = some 13 := by decide +kernel
-- ComputeLookupSection2Label2
example :
    (sptLookup 2 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 2) = some 20 := by decide +kernel

private def checkEq (name : String) (actual expected : String) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

/-- Runtime replay of the 13 probe rows through `repr`, available for the
exact `Line`/`Section`/`Spt` carriers. -/
def runChecks : IO Bool := do
  let results ← [
    checkEq "lab_to_target labels SectionLabelsEmpty"
      (reprStr (sectionLabels 5 ([] : List L) [])) (reprStr ((5, []) : Nat × List (Nat × Nat))),
    checkEq "lab_to_target labels SectionLabelsEmptyLabs"
      (reprStr (sectionLabels 5 ([] : List L) [(9, 9)]))
      (reprStr ((5, [(9, 9)]) : Nat × List (Nat × Nat))),
    checkEq "lab_to_target labels SectionLabelsConcrete"
      (reprStr (sectionLabels 10 lines []))
      (reprStr ((22, [(2, 17), (1, 13)]) : Nat × List (Nat × Nat))),
    checkEq "lab_to_target labels SectionLabelsConcreteLabs"
      (reprStr (sectionLabels 10 lines [(7, 7)]))
      (reprStr ((22, [(2, 17), (1, 13), (7, 7)]) : Nat × List (Nat × Nat))),
    checkEq "lab_to_target labels ComputeLabelsAltEmpty"
      (reprStr (computeLabelsAlt 5 ([] : List S) (.ln : Spt (Spt Nat))))
      (reprStr (.ln : Spt (Spt Nat))),
    checkEq "lab_to_target labels ComputeLabelsAltConcrete"
      (reprStr (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat))))
      (reprStr (sptInsert 2 (sptFromAList [(0, 13), (2, 20)])
        (sptInsert 1 (sptFromAList [(0, 10), (1, 13)]) .ln))),
    checkEq "lab_to_target labels ComputeLookupSection1"
      (reprStr (sptLookup 1 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))))
      (reprStr (some (sptFromAList [(0, 10), (1, 13)]))),
    checkEq "lab_to_target labels ComputeLookupSection2"
      (reprStr (sptLookup 2 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))))
      (reprStr (some (sptFromAList [(0, 13), (2, 20)]))),
    checkEq "lab_to_target labels ComputeLookupSection3Absent"
      (reprStr (sptLookup 3 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))))
      (reprStr (none : Option (Spt Nat))),
    checkEq "lab_to_target labels ComputeLookupSection1Start"
      (reprStr ((sptLookup 1 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 0))) (reprStr (some 10)),
    checkEq "lab_to_target labels ComputeLookupSection1Label1"
      (reprStr ((sptLookup 1 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 1))) (reprStr (some 13)),
    checkEq "lab_to_target labels ComputeLookupSection2Start"
      (reprStr ((sptLookup 2 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 0))) (reprStr (some 13)),
    checkEq "lab_to_target labels ComputeLookupSection2Label2"
      (reprStr ((sptLookup 2 (computeLabelsAlt 10 [sec1, sec2] (.ln : Spt (Spt Nat)))).bind
        (sptLookup 2))) (reprStr (some 20))
    ].mapM id
  pure (results.all id)

end Flapjack.Test.LabToTargetLabelsParity
