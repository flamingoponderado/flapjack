import Flapjack.Compiler.Backend.LabToTarget.SectionNopEncoding
namespace Flapjack.Test.LabToTargetSectionNopEncodingParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w]
  | .jumpCmp _ _ _ w => [w]
  | .loc _ w => [w]
  | _ => [0]
private def aux : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [0] 1]
private def code : List (LabLineHOL 8) := [.label 1 9 1,.labAsm (.jump (.lab 1 2)) 77 [249] 3,
  .label 1 10 0,.asm (.asmi (.inst .skip)) [0] 1,.labAsm .halt 88 [229] 2,.labAsm (.call (.lab 1 2)) 99 [0] 2]
private theorem auxValid : linesEncWithNop enc .ln [] 5 aux.reverse := by
  change linesEncWithNop enc .ln [] 5 [.asm (.asmi (.inst .skip)) [0] 1,.label 1 2 0]
  simp only [linesEncWithNop,lineEncWithNop,encWithNop]
  decide +kernel
private theorem guards : [0] = enc (.inst .skip) ∧ ([0] : List (BitVec 8)).length = 1 ∧
    linesEncd enc .ln [] (5+(aux.map lineLen).sum) code ∧
    linesEncWithNop enc .ln [] 5 aux.reverse ∧
    ¬(∀ l ∈ aux, isLabelHOL l = true) ∧ (∀ l ∈ code, labelOne l) := by
  refine ⟨rfl,rfl,?_,auxValid,?_,?_⟩
  · simp only [aux,code,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lineLen,
      linesEncd,lineEncd]
    decide +kernel
  · simp [aux,isLabelHOL]
  · simp [code,labelOne]
example : linesEncWithNop enc .ln [] 5 (padSection [0] code aux) :=
  linesEncWithNop_padSection1 enc .ln [] [0] code aux 5 guards
example : padSection [0] code aux = [.asm (.asmi (.inst .skip)) [0,0] 2,.label 1 2 0,
    .label 1 9 0,.labAsm (.jump (.lab 1 2)) 77 [249,0,0] 3,.label 1 10 0,
    .asm (.asmi (.inst .skip)) [0] 1,.labAsm .halt 88 [229,0] 2,.labAsm (.call (.lab 1 2)) 99 [0,0] 2] := by
  rfl
example : padSection [0] [.label 1 9 1,.label 1 10 1] aux =
    [.asm (.asmi (.inst .skip)) [0,0,0] 3,.label 1 2 0,.label 1 9 0,.label 1 10 0] ∧
    linesEncWithNop enc .ln [] 5 (padSection [0] [.label 1 9 1,.label 1 10 1] aux) := by
  refine ⟨by rfl,linesEncWithNop_padSection1 enc .ln [] [0] _ aux 5 ?_⟩
  refine ⟨rfl,rfl,by simp [linesEncd,lineEncd],auxValid,by simp [aux,isLabelHOL],by simp [labelOne]⟩
example : padSection [0] [.label 1 9 0] aux = aux.reverse ++ [.label 1 9 0] := by rfl
example : padSection [0] [] aux = aux.reverse := rfl

/-- All seven native LabAsm constructors have real successful source guards
and consume the full theorem, including arbitrary FFI/label/register payloads. -/
private theorem allLabConstructor (a : AsmWithLab HolCmp (HolRegImm 8) MlString) :
    linesEncd (fun _ : HolAsm 8 => [0]) .ln [] 6 [.labAsm a 77 [0] 3] ∧
    linesEncWithNop (fun _ : HolAsm 8 => [0]) .ln [] 5
      (padSection [0] [.labAsm a 77 [0] 3] aux) := by
  have hc : linesEncd (fun _ : HolAsm 8 => [0]) .ln [] 6 [.labAsm a 77 [0] 3] := by
    cases a <;> simp [linesEncd,lineEncd]
  refine ⟨hc,linesEncWithNop_padSection1 (fun _ : HolAsm 8 => [0]) .ln [] [0] _ aux 5 ?_⟩
  refine ⟨rfl,rfl,?_,?_,by simp [aux,isLabelHOL],by simp [labelOne]⟩
  · simpa [aux,lineLen] using hc
  · change linesEncWithNop (fun _ : HolAsm 8 => [0]) .ln [] 5
      [.asm (.asmi (.inst .skip)) [0] 1,.label 1 2 0]
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
    nop = enc (.inst .skip) ∧ nop.length = 1 ∧
    linesEncd enc labs ffis (pos + (aux.map lineLen).sum) code ∧
    linesEncWithNop enc labs ffis pos aux.reverse ∧
    ¬(∀ l ∈ aux, isLabelHOL l = true) ∧ (∀ l ∈ code, labelOne l) →
    linesEncWithNop enc labs ffis pos (padSection nop code aux) :=
  linesEncWithNop_padSection1 enc labs ffis nop code aux pos

def runChecks : IO Bool := do
  IO.println "PASS full one-byte section NOP encoding (13 original observations; offset-sensitive mixed code, repeated labels and all seven LabAsm constructors)"
  pure true
end Flapjack.Test.LabToTargetSectionNopEncodingParity
