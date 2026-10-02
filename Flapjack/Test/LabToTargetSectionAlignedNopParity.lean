import Flapjack.Compiler.Backend.LabToTarget.SectionNopEncoding
namespace Flapjack.Test.LabToTargetSectionAlignedNopParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w,w]
  | .jumpCmp _ _ _ w => [w,w]
  | .loc _ w => [w,w]
  | _ => [0,0]
private def aux : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [0,0] 2]
private def code : List (LabLineHOL 8) := [.labAsm (.jump (.lab 1 2)) 77 [249,249] 6,
  .label 1 9 0,.labAsm .halt 88 [227,227] 4]
private theorem auxValid : linesEncWithNop enc .ln [] 5 aux.reverse := by
  change linesEncWithNop enc .ln [] 5 [.asm (.asmi (.inst .skip)) [0,0] 2,.label 1 2 0]
  simp only [linesEncWithNop,lineEncWithNop,encWithNop]
  decide +kernel
private theorem guards : [0,0] = enc (.inst .skip) ∧ 0<([0,0] : List (BitVec 8)).length ∧
    (∀ l ∈ code,lineAligned 2 l) ∧ linesEncd enc .ln [] (5+(aux.map lineLen).sum) code ∧
    linesEncWithNop enc .ln [] 5 aux.reverse ∧ ¬(∀ l ∈ aux,isLabelHOL l=true) ∧ (∀ l ∈ code,labelZero l) := by
  refine ⟨rfl,by decide +kernel,?_,?_,auxValid,by simp [aux,isLabelHOL],by simp [code,labelZero]⟩
  · simp [code,lineAligned,lineLen,lineLength]
  · simp only [code,aux,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lineLen,linesEncd,lineEncd]
    decide +kernel
example : linesEncWithNop enc .ln [] 5 (padSection [0,0] code aux) :=
  linesEncWithNop_padSection01 enc .ln [] [0,0] code aux 5 guards
example : padSection [0,0] code aux = [.asm (.asmi (.inst .skip)) [0,0] 2,.label 1 2 0,
    .labAsm (.jump (.lab 1 2)) 77 [249,249,0,0,0,0] 6,.label 1 9 0,.labAsm .halt 88 [227,227,0,0] 4] := rfl
example : linesEncWithNop enc .ln [] 5 (padSection [0,0] [] aux) :=
  linesEncWithNop_padSection01 enc .ln [] [0,0] [] aux 5
    ⟨rfl,by decide +kernel,by simp,trivial,auxValid,by simp [aux,isLabelHOL],by simp⟩
private def shortenc : HolAsm 8 → List (BitVec 8)
  | .inst .skip => [0,0]
  | _ => [7]
example : lineEncd shortenc .ln [] 7 (.labAsm .halt 77 [7] 4) ∧
    ¬lineAligned (width := 8) 2 (.labAsm .halt 77 [7] 4) ∧
    ¬lineEncWithNop shortenc .ln [] 7 (.labAsm .halt 77 (padBytes [7] 4 [0,0]) 4) := by
  simp only [lineEncd,lineAligned,lineLen,lineLength,lineEncWithNop,encWithNop]
  decide +kernel
example : lineEncd enc .ln [] 7 (.labAsm (.jump (.lab 1 2)) 77 [249,249] 3) ∧
    ¬lineAligned (width := 8) 2 (.labAsm (.jump (.lab 1 2)) 77 [249,249] 3) ∧
    ¬lineEncWithNop enc .ln [] 7 (.labAsm (.jump (.lab 1 2)) 77 (padBytes [249,249] 3 [0,0]) 3) := by
  simp only [lineEncd,lineAligned,lineLen,lineLength,lineEncWithNop,encWithNop]
  decide +kernel
private theorem allLabConstructor (a : AsmWithLab HolCmp (HolRegImm 8) MlString) :
    linesEncd (fun _ : HolAsm 8 => [0,0]) .ln [] 7 [.labAsm a 77 [0,0] 6] ∧
    lineAligned (width := 8) 2 (.labAsm a 77 [0,0] 6) ∧
    linesEncWithNop (fun _ : HolAsm 8 => [0,0]) .ln [] 5 (padSection [0,0] [.labAsm a 77 [0,0] 6] aux) := by
  have hc : linesEncd (fun _ : HolAsm 8 => [0,0]) .ln [] 7 [.labAsm a 77 [0,0] 6] := by
    cases a <;> simp [linesEncd,lineEncd]
  have hal : lineAligned (width := 8) 2 (.labAsm a 77 [0,0] 6) := by simp [lineAligned,lineLen,lineLength]
  refine ⟨hc,hal,linesEncWithNop_padSection01 (fun _ : HolAsm 8 => [0,0]) .ln [] [0,0] _ aux 5 ?_⟩
  refine ⟨rfl,by decide +kernel,by simpa using hal,?_,?_,by simp [aux,isLabelHOL],by simp [labelZero]⟩
  · simpa [aux,lineLen] using hc
  · change linesEncWithNop (fun _ : HolAsm 8 => [0,0]) .ln [] 5 [.asm (.asmi (.inst .skip)) [0,0] 2,.label 1 2 0]
    simp [linesEncWithNop,lineEncWithNop,encWithNop]
example := allLabConstructor (.jump (.lab 1 2))
example := allLabConstructor (.jumpCmp .equal 0 (.reg 1) (.lab 1 2))
example := allLabConstructor (.locValue 0 (.lab 1 2))
example := allLabConstructor (.call (.lab 1 2))
example := allLabConstructor (.callFFI (.implode []))
example := allLabConstructor (.install)
example := allLabConstructor (.halt)
example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (nop : List (BitVec 8)) (code aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    nop = enc (.inst .skip) ∧ 0 < nop.length ∧ (∀ l ∈ code,lineAligned nop.length l) ∧
    linesEncd enc labs ffis (pos+(aux.map lineLen).sum) code ∧ linesEncWithNop enc labs ffis pos aux.reverse ∧
    ¬(∀ l ∈ aux,isLabelHOL l=true) ∧ (∀ l ∈ code,labelZero l) →
    linesEncWithNop enc labs ffis pos (padSection nop code aux) := linesEncWithNop_padSection01 enc labs ffis nop code aux pos

def runChecks : IO Bool := do
  IO.println "PASS full positive-length aligned section NOP encoding (13 original observations, multibyte offsets, both divisibility guard counterexamples, all seven LabAsm constructors)"
  pure true
end Flapjack.Test.LabToTargetSectionAlignedNopParity
