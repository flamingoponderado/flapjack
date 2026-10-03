import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
import Flapjack.Compiler.Backend.LabToTarget.ShmemExtraction
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original enumeration bound.
Both source guards remain and no desired position bound is assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "genlist_line_to_info_entry_pc_max" (words_as_type_indexed_bitvec)]
theorem genlistLineToInfo_entryPcMax {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncOk c labs ffis validPos code ∧ encOk c →
    ∀ x ∈ ((List.range (numPcs code)).map
      (fun i => lineToInfo code 0 (i,asmFetchAux i code))).flatten,
      x.2.entryPc < posVal (numPcs code) 0 code := by
  rintro ⟨he,hc⟩ x hx
  obtain ⟨entries,hentries,hx⟩ := List.mem_flatten.mp hx
  obtain ⟨pc,hpc,rfl⟩ := List.mem_map.mp hentries
  have hbound : pc < numPcs code := List.mem_range.mp hpc
  have hpos := posVal_mono pc 0 code (numPcs code) validPos c labs ffis
    ⟨hbound,Nat.le_refl _,he,hc⟩
  cases hf : asmFetchAux pc code with
  | none => simp [lineToInfo,hf] at hx
  | some line =>
    cases line with
    | label a b n => simp [lineToInfo,hf] at hx
    | labAsm a w bytes len => simp [lineToInfo,hf] at hx
    | asm inst bytes len =>
      cases inst with
      | asmi inst => simp [lineToInfo,hf] at hx
      | cbw a b => simp [lineToInfo,hf] at hx
      | shareMem op reg addr =>
        cases addr
        rcases hm : getMemopInfo op with ⟨name,nb⟩
        simp only [lineToInfo,hf,hm,List.mem_singleton] at hx
        subst x
        exact hpos
end Flapjack.Compiler.Backend.LabToTarget
