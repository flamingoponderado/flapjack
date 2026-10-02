import Flapjack.Compiler.Backend.LabToTarget.SectionNopEncoding
namespace Flapjack.Test.LabToTargetSectionPrefixNopParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w]
  | .jumpCmp _ _ _ w => [w]
  | .loc _ w => [w]
  | _ => [0]
private def aux : List (LabLineHOL 8) := [.label 1 2 0,.label 1 3 0]
private def code : List (LabLineHOL 8) := [.label 1 9 0,.labAsm (.jump (.lab 1 2)) 77 [251] 3,
  .label 1 10 1,.asm (.asmi (.inst .skip)) [0] 1]
private theorem auxValid : linesEncWithNop enc .ln [] 5 aux.reverse := by
  change linesEncWithNop enc .ln [] 5 [.label 1 3 0,.label 1 2 0]
  simp [linesEncWithNop,lineEncWithNop]
private theorem auxLabels : ∀ l ∈ aux, isLabelHOL l = true := by simp [aux,isLabelHOL]
private theorem mixedGuards : [0] = enc (.inst .skip) ∧ ([0] : List (BitVec 8)).length = 1 ∧
    linesEncd enc .ln [] (5+(aux.map lineLen).sum) code ∧
    linesEncWithNop enc .ln [] 5 aux.reverse ∧
    (∀ l ∈ aux, isLabelHOL l = true) ∧ (∀ l ∈ code, labelOne l) ∧ labelPrefixZero code := by
  refine ⟨rfl,rfl,?_,auxValid,auxLabels,?_,?_⟩
  · simp only [aux,code,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lineLen,linesEncd,lineEncd]
    decide +kernel
  · simp [code,labelOne]
  · simp [code,isLabelHOL,lineLen]
example : linesEncWithNop enc .ln [] 5 (padSection [0] code aux) :=
  linesEncWithNop_padSection enc .ln [] [0] code aux 5 mixedGuards
example : padSection [0] code aux = [.label 1 3 0,.label 1 2 0,.label 1 9 0,
    .labAsm (.jump (.lab 1 2)) 77 [251,0,0,0] 4,.label 1 10 0,.asm (.asmi (.inst .skip)) [0] 1] := rfl
example : linesEncd enc .ln [] 5 [.label 1 9 1,.labAsm (.jump (.lab 1 2)) 77 [250] 1] ∧
    (∀ l ∈ [.label 1 9 1,.labAsm (.jump (.lab 1 2)) 77 [250] 1],labelOne (width := 8) l) ∧
    ¬labelPrefixZero (width := 8) [.label 1 9 1,.labAsm (.jump (.lab 1 2)) 77 [250] 1] ∧
    ¬linesEncWithNop enc .ln [] 5 (padSection [0] [.label 1 9 1,.labAsm (.jump (.lab 1 2)) 77 [250] 1] aux) := by
  refine ⟨?_,by simp [labelOne],by simp [isLabelHOL,lineLen],?_⟩
  · simp only [linesEncd,lineEncd,lineLen]
    decide +kernel
  · change ¬linesEncWithNop enc .ln [] 5 [.label 1 3 0,.label 1 2 0,.label 1 9 0,.labAsm (.jump (.lab 1 2)) 77 [250] 1]
    simp only [linesEncWithNop,lineEncWithNop,encWithNop]
    decide +kernel
example : linesEncd enc .ln [] 5 [.label 1 9 0,.asm (.asmi (.inst .skip)) [0] 1] ∧
    linesEncWithNop enc .ln [] 5 (padSection [0] [.label 1 9 0,.asm (.asmi (.inst .skip)) [0] 1] []) := by
  have hc : linesEncd enc .ln [] 5 [.label 1 9 0,.asm (.asmi (.inst .skip)) [0] 1] := by
    simp only [linesEncd,lineEncd]
    decide +kernel
  refine ⟨hc,linesEncWithNop_padSection enc .ln [] [0] _ [] 5 ?_⟩
  refine ⟨rfl,rfl,by simpa using hc,by simp [linesEncWithNop],by simp,by simp [labelOne],by simp [isLabelHOL,lineLen]⟩
example : linesEncWithNop enc .ln [] 5 (padSection [0] [.label 1 9 0,.label 1 10 0] aux) := by
  apply linesEncWithNop_padSection enc .ln [] [0] _ aux 5
  refine ⟨rfl,rfl,by simp [linesEncd,lineEncd],auxValid,auxLabels,by simp [labelOne],by simp [isLabelHOL,lineLen]⟩
example : linesEncWithNop enc .ln [] 5 (padSection [0] [] aux) :=
  linesEncWithNop_padSection enc .ln [] [0] [] aux 5 ⟨rfl,rfl,trivial,auxValid,auxLabels,by simp,by simp⟩
example : linesEncd enc .ln [] 5 [.labAsm (.call (.lab 1 2)) 77 [0] 3,.label 1 9 1,.asm (.asmi (.inst .skip)) [0] 1] ∧
    labelPrefixZero (width := 8) [.labAsm (.call (.lab 1 2)) 77 [0] 3,.label 1 9 1,.asm (.asmi (.inst .skip)) [0] 1] ∧
    linesEncWithNop enc .ln [] 5 (padSection [0] [.labAsm (.call (.lab 1 2)) 77 [0] 3,.label 1 9 1,.asm (.asmi (.inst .skip)) [0] 1] aux) := by
  have hc : linesEncd enc .ln [] 5 [.labAsm (.call (.lab 1 2)) 77 [0] 3,.label 1 9 1,.asm (.asmi (.inst .skip)) [0] 1] := by
    simp only [linesEncd,lineEncd]
    decide +kernel
  refine ⟨hc,by simp [isLabelHOL],linesEncWithNop_padSection enc .ln [] [0] _ aux 5 ?_⟩
  refine ⟨rfl,rfl,?_,auxValid,auxLabels,by simp [labelOne],by simp [isLabelHOL]⟩
  simpa [aux,lineLen] using hc
example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (nop : List (BitVec 8)) (code aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    nop = enc (.inst .skip) ∧ nop.length = 1 ∧
    linesEncd enc labs ffis (pos + (aux.map lineLen).sum) code ∧
    linesEncWithNop enc labs ffis pos aux.reverse ∧
    (∀ l ∈ aux, isLabelHOL l = true) ∧ (∀ l ∈ code, labelOne l) ∧ labelPrefixZero code →
    linesEncWithNop enc labs ffis pos (padSection nop code aux) :=
  linesEncWithNop_padSection enc labs ffis nop code aux pos

def runChecks : IO Bool := do
  IO.println "PASS full all-label prefix-safe section NOP encoding (8 original observations, actual theorem instances and necessary prefix guard counterexample)"
  pure true
end Flapjack.Test.LabToTargetSectionPrefixNopParity
