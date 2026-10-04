import Flapjack.Compiler.Backend.LabToTarget.ShmemExtraction
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original name projection offset equation. The two word dimensions are independent. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineToInfo_offsetNames {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth))
      (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat)
    (accum : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth))
      (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    (lineToInfo code p accum).map Prod.fst =
      (lineToInfo code 0 accum).map Prod.fst := by
  rcases accum with ⟨pc,fetched⟩
  cases fetched with
  | none => rfl
  | some line =>
    cases line with
    | label a b n => rfl
    | labAsm a w bytes len => rfl
    | asm inst bytes len =>
      cases inst with
      | asmi inst => rfl
      | cbw a b => rfl
      | shareMem op reg addr => cases addr; rfl

/-- Full independent-carrier line-record offset equation; no desired record
or encoding hypothesis is supplied. Both original word dimensions remain independent. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineToInfo_offsetRecords {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth))
      (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat)
    (accum : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth))
      (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    (lineToInfo code p accum).map Prod.snd =
      (lineToInfo code 0 accum).map (fun x =>
        {x.2 with entryPc:=p+x.2.entryPc,exitPc:=p+x.2.exitPc}) := by
  rcases accum with ⟨pc,fetched⟩
  cases fetched with
  | none => rfl
  | some line =>
    cases line with
    | label a b n => rfl
    | labAsm a w bytes len => rfl
    | asm inst bytes len =>
      cases inst with
      | asmi inst => rfl
      | cbw a b => rfl
      | shareMem op reg addr =>
        cases addr
        rcases hm : getMemopInfo op with ⟨name,nb⟩
        have hp := posVal_accZero pc p code
        simp only [lineToInfo,hm,List.map_cons,List.map_nil]
        rw [←hp]
        simp only [Nat.add_assoc]
/-- Full original initial-PC offset conjunction. The sole original encoding
validity guard and independent validity/query positions remain quantified. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getShmemInfo_initPcOffset {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) :
    allEncOk c labs ffis validPos code →
      (getShmemInfo code 0 [] []).1 = (getShmemInfo code p [] []).1 ∧
      ((getShmemInfo code 0 [] []).2.map (fun record =>
        {record with entryPc:=p+record.entryPc,exitPc:=p+record.exitPc})) =
        (getShmemInfo code p [] []).2 := by
  intro he
  rw [getShmemInfo_characterization code 0 [] [] validPos c labs ffis he,
      getShmemInfo_characterization code p [] [] validPos c labs ffis he]
  simp only [List.unzip_eq_map,List.nil_append]
  constructor
  · rw [List.map_flatten,List.map_flatten]
    apply congrArg List.flatten
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro x _
    exact (lineToInfo_offsetNames code p (x,asmFetchAux x code)).symm
  · rw [List.map_map,List.map_flatten,List.map_flatten]
    apply congrArg List.flatten
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro x _
    exact (lineToInfo_offsetRecords code p (x,asmFetchAux x code)).symm
end Flapjack.Compiler.Backend.LabToTarget
