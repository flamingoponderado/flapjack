import Flapjack.Compiler.Backend.LabProps.LabelSets
import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.LabProps.SectionEnd
import Flapjack.Compiler.Backend.LabProps.Native
import Flapjack.Compiler.Backend.BackendProps
import Flapjack.Compiler.Backend.LabToTarget.LabsDomain

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Complete original seven-conjunct oracle-code invariant. The label tree's
value carrier is the independently generic source β, not the word dimension
and not a specialization to natural offsets. Source EVERY/ALL_DISTINCT
are universal list membership and Nodup with ordinary equality. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def goodCode {width : Nat} [NeZero width] {β : Type}
    (c : AsmConfigExact width) (labs : Spt (Spt β)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  (∀ sec ∈ code, LabProps.secEndsWithLabelNative sec) ∧
  (∀ sec ∈ code, LabProps.secLabelsOk sec) ∧
  (code.map Section.sectionId).Nodup ∧
  (∀ sec ∈ code, (LabProps.LabelSets.extractLabels sec.lines).Nodup) ∧
  Disjoint (α := Set Nat) (Set.ofPred (sptDomain labs)) {n | n ∈ code.map Section.sectionId} ∧
  BackendProps.restrictNonzero (LabProps.LabelSets.getLabels code) ⊆
    LabProps.LabelSets.getCodeLabels code ∪ labsDomain labs ∧
  LabProps.allEncOkPreHOL c code

end Flapjack.Compiler.Backend.LabToTarget
