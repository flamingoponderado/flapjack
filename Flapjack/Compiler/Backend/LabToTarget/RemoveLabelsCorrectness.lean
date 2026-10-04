import Flapjack.Compiler.Backend.LabToTarget.RemoveLabelsLoop
import Flapjack.Compiler.Backend.LabToTarget.InitialEncodingPreconditions
import Flapjack.Compiler.Backend.LabToTarget.InitialEncodingNavigation
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original label-removal pass theorem, preserving all eleven original
guards and all six conclusions. Initial encoding establishes the genuine loop
preconditions; the complete loop theorem supplies actual output validity and
every returned-label property. No simulation or returned-state facts are assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeLabels_correct {width : Nat} [NeZero width]
    (clock : Nat) (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName)
    (code output : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (labs : Spt (Spt Nat)) :
    removeLabels clock c pos acc ffis code = some (output,labs) ∧ encOk c ∧
    (∀ sec ∈ code,secEndsWithLabelNative sec) ∧
    (∀ sec ∈ code,secLabelsOk sec) ∧ (code.map Section.sectionId).Nodup ∧
    (∀ sec ∈ code,(extractLabels sec.lines).Nodup) ∧
    Disjoint (sptDomain acc) {n | n ∈ code.map Section.sectionId} ∧
    restrictNonzero (getLabels code) ⊆ getCodeLabels code ∪ labsDomain acc ∧
    allEncOkPreHOL c code ∧ pos % 2 = 0 ∧
    (∀ sid lid,match labLookup sid lid acc with
      | none => True
      | some value => value % 2 = 0) →
    allEncOk c labs ffis pos output ∧ codeSimilar code output ∧
    (hasOddInst output → c.codeAlignment = 0) ∧
    (∀ sid lid value,labLookup sid lid labs = some value → value % 2 = 0) ∧
    (∀ sid lid value,labLookup sid lid acc = some value → labLookup sid lid labs = some value) ∧
    (∀ sid lid pc,locToPc sid lid code = some pc →
      labLookup sid lid labs = some (posVal pc pos output)) := by
  rintro ⟨he,hencoder,hends,hvalid,hids,hlabels,hdis,hsub,hpre,heven,hacc⟩
  let initial := encSecList c.encode code
  have hsBack := (codeSimilar_encSecList code code c.encode).mpr (codeSimilar_refl code)
  have hs := codeSimilar_sym initial code hsBack
  have hi := codeSimilar_sectionNumbers code initial hs
  have hl := codeSimilar_extractedLabels code initial hs
  have hLab := codeSimilar_labels code initial hs
  have hCodeLab := codeSimilar_codeLabels code initial hs
  have hDistinct : ∀ sec ∈ initial,(extractLabels sec.lines).Nodup := by
    have hh : ∀ ls ∈ code.map (fun sec => extractLabels sec.lines),ls.Nodup := by
      simpa only [List.forall_mem_map] using hlabels
    rw [hl] at hh
    simpa only [List.forall_mem_map] using hh
  have hLoop := removeLabelsLoop_correct clock c pos acc ffis initial output labs
    ⟨he,encSecList_endsWithLabel c.encode code hends,
      encSecList_secLabelsOk c.encode code hvalid,
      hi ▸ hids,hDistinct,
      by simpa only [hi] using hdis,
      by simpa only [hLab,hCodeLab] using hsub,
      encSecList_pre code c.encode c hpre,
      encSecList_encd0 c.encode code,hencoder,heven,hacc⟩
  rcases hLoop with ⟨_,_,hOk,hSimilar,hOdd,hEven,hPreserve,hLookup⟩
  refine ⟨hOk,codeSimilar_trans code initial output ⟨hs,hSimilar⟩,hOdd,hEven,hPreserve,?_⟩
  intro sid lid pc hp
  apply hLookup sid lid pc
  change locToPc sid lid (encSecList c.encode code) = some pc
  rw [locToPc_encSecList sid lid code c.encode]
  exact hp
end Flapjack.Compiler.Backend.LabToTarget
