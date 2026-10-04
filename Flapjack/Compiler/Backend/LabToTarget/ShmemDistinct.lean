import Flapjack.Compiler.Backend.LabToTarget.ShmemExtraction
import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack constructor infrastructure: an extraction contributes at most
one PC, which is exactly the position of its enumerated instruction. -/
private theorem lineInfo_entry {width : Nat} [NeZero width]
    (code : LabProgHOL width) (p i : Nat) (line : Option (LabLineHOL width)) :
    ((lineToInfo code p (i,line)).map (fun x => x.2.entryPc)).Nodup ∧
    ∀ x ∈ (lineToInfo code p (i,line)).map (fun x => x.2.entryPc), x = posVal i p code := by
  cases line with
  | none => simp [lineToInfo]
  | some line =>
    cases line with
    | label a b n => simp [lineToInfo]
    | labAsm a w bs n => simp [lineToInfo]
    | asm a bs n =>
      cases a with
      | asmi a => simp [lineToInfo]
      | cbw a b => simp [lineToInfo]
      | shareMem m r addr =>
        cases addr
        simp [lineToInfo]

/-- Full original entry-PC distinctness. All three source guards remain,
including the word-dimensional emitted-size bound. Entry PCs and arbitrary
query/validity starts are Nat, exactly as in the original record carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getShmemInfo_entryDistinct {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos p : Nat) :
    (progToBytes code).length < 2^width ∧ encOk c ∧ allEncOk c labs ffis validPos code →
    ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc).Nodup := by
  rintro ⟨_hsize,hc,he⟩
  rw [getShmemInfo_characterization code p [] [] validPos c labs ffis he]
  simp only [List.unzip_eq_map,List.nil_append,List.map_map,Function.comp_def]
  rw [List.map_flatten]
  simp only [List.map_map,Function.comp_def]
  change (List.flatMap (fun i => (lineToInfo code p (i,asmFetchAux i code)).map
    (fun x => x.2.entryPc)) (List.range (numPcs code))).Nodup
  rw [List.Nodup,List.pairwise_flatMap]
  constructor
  · intro i _
    exact (lineInfo_entry code p i (asmFetchAux i code)).1
  · apply List.Pairwise.imp_of_mem (p := List.pairwise_lt_range)
    intro i j _hi hj hij x hx y hy
    have hxpos := (lineInfo_entry code p i (asmFetchAux i code)).2 x hx
    have hypos := (lineInfo_entry code p j (asmFetchAux j code)).2 y hy
    have hjbound : j < numPcs code := List.mem_range.mp hj
    have hstrict := posVal_mono i p code j validPos c labs ffis
      ⟨hij,by omega,he,hc⟩
    omega
end Flapjack.Compiler.Backend.LabToTarget
