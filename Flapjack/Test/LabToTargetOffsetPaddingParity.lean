import Flapjack.Compiler.Backend.LabToTarget.OffsetPadding
namespace Flapjack.Test.LabToTargetOffsetPaddingParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def aux : List (LabLineHOL 8) := [.asm (.asmi (.inst .skip)) [9] 3]
private def lines : List (LabLineHOL 8) := [.label 1 2 1,.label 1 3 0,.labAsm .halt 236 [5,6] 3,.label 1 4 1]
private def result : List (LabLineHOL 8) := [.asm (.asmi (.inst .skip)) [9,0] 4,
  .label 1 2 0,.label 1 3 0,.labAsm .halt 236 [5,6,0,0] 4,.label 1 4 0]
private theorem guards : labLenPosOk (0+(aux.map lineLen).sum) lines ∧ labLenPosOk 0 aux.reverse ∧
    (∀ l ∈ aux,labelZero l) ∧
    ((match lines with | .label _ _ len :: _ => len = 1 | _ => False) →
      (match aux with | [] => False | x :: _ => isLabelHOL x ≠ true)) ∧
    linesOffsetOk .ln [] 0 (aux.reverse++lines) := by
  simp [lines,aux,labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk,labelZero,isLabelHOL]
  all_goals decide +kernel
example : labLenPosOk (0+(aux.map lineLen).sum) lines ∧ labLenPosOk 0 aux.reverse ∧
    (∀ l ∈ aux,labelZero l) ∧
    ((match lines with | .label _ _ len :: _ => len = 1 | _ => False) →
      (match aux with | [] => False | x :: _ => isLabelHOL x ≠ true)) ∧
    linesOffsetOk .ln [] 0 (aux.reverse++lines) := guards
example : padSection [0] lines aux = result := rfl
example : linesOffsetOk .ln [] 0 (padSection [0] lines aux) := linesOffsetOk_padSection [0] lines aux .ln [] 0 guards
example : padSection [] lines aux = [.asm (.asmi (.inst .skip)) [9] 4,
    .label 1 2 0,.label 1 3 0,.labAsm .halt 236 [5,6] 4,.label 1 4 0] ∧
    linesOffsetOk .ln [] 0 (padSection [] lines aux) := ⟨rfl,linesOffsetOk_padSection [] lines aux .ln [] 0 guards⟩
example : padSection [7,8] lines aux = [.asm (.asmi (.inst .skip)) [9,7,8] 4,
    .label 1 2 0,.label 1 3 0,.labAsm .halt 236 [5,6,7,7,8] 4,.label 1 4 0] ∧
    linesOffsetOk .ln [] 0 (padSection [7,8] lines aux) := ⟨rfl,linesOffsetOk_padSection [7,8] lines aux .ln [] 0 guards⟩
example : linesOffsetOk (width := 8) .ln [] 0
    (padSection [0] [.label 1 3 0,.labAsm .halt 238 [] 2] [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 2]) := by
  apply linesOffsetOk_padSection
  simp [labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk,labelZero,isLabelHOL]
  all_goals decide +kernel
example : linesOffsetOk (width := 8) .ln [] 0 (padSection [0] [.labAsm .halt 240 [] 3,.label 1 2 1] []) := by
  apply linesOffsetOk_padSection
  simp [labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk,labelZero]
  all_goals decide +kernel
example : labLenPosOk (width := 8) 1 [.label 1 2 1,.labAsm .halt 238 [] 0] ∧
    linesOffsetOk (width := 8) .ln [] 1 [.label 1 2 1,.labAsm .halt 238 [] 0] ∧
    ¬linesOffsetOk (width := 8) .ln [] 1 (padSection [0] [.label 1 2 1,.labAsm .halt 238 [] 0] []) := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk,padSection,addNop]
  all_goals decide +kernel
example : ¬labLenPosOk (width := 8) 2 [.label 1 2 2,.labAsm .halt 236 [] 0] ∧
    linesOffsetOk (width := 8) .ln [] 0 [.asm (.asmi (.inst .skip)) [] 2,.label 1 2 2,.labAsm .halt 236 [] 0] ∧
    ¬linesOffsetOk (width := 8) .ln [] 0
      (padSection [0] [.label 1 2 2,.labAsm .halt 236 [] 0] [.asm (.asmi (.inst .skip)) [] 2]) := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk,padSection,addNop]
  all_goals decide +kernel
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def ffis : List HolFfiName := [.extCall (.implode [97]),.extCall (.implode []),.extCall (.implode [])]
private theorem allConstructor (a : AsmWithLab HolCmp (HolRegImm 8) MlString) :
    linesOffsetOk labs ffis 0 (padSection [0]
      [.labAsm a (getJumpOffset a ffis labs 0) [] 3,.label 1 2 1] []) := by
  apply linesOffsetOk_padSection
  simp [labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk]
example := allConstructor (.jump (.lab 3 4))
example := allConstructor (.jumpCmp .equal 2 (.imm 1) (.lab 3 4))
example := allConstructor (.locValue 2 (.lab 3 4))
example := allConstructor (.call (.lab 3 4))
example := allConstructor (.callFFI (.implode []))
example := allConstructor .install
example := allConstructor .halt
example : linesOffsetOk (width := 1) .ln [] 17 (padSection [0] [] []) :=
  linesOffsetOk_padSection [0] [] [] .ln [] 17 (by simp [labLenPosOk,linesOffsetOk])
example : padSection (width := 80) [7] [.labAsm .halt (BitVec.ofNat 80 (2^80-16)) [] 3,.label 1 2 1] [] =
    [.labAsm .halt (BitVec.ofNat 80 (2^80-16)) [7,7,7,7] 4,.label 1 2 0] ∧
    linesOffsetOk (width := 80) .ln [] (2^80)
      (padSection [7] [.labAsm .halt (BitVec.ofNat 80 (2^80-16)) [] 3,.label 1 2 1] []) := by
  refine ⟨rfl,?_⟩
  apply linesOffsetOk_padSection
  simp [labLenPosOk,lineLabLenPosOk,lineLen,linesOffsetOk,lineOffsetOk,labelZero]
  all_goals decide +kernel
example {width : Nat} [NeZero width] (nop : List (BitVec 8)) (lines aux : List (LabLineHOL width))
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat) :
    labLenPosOk (pos+(aux.map lineLen).sum) lines ∧ labLenPosOk pos aux.reverse ∧
    (∀ l ∈ aux,labelZero l) ∧
    ((match lines with | .label _ _ len :: _ => len = 1 | _ => False) →
      (match aux with | [] => False | x :: _ => isLabelHOL x ≠ true)) ∧
    linesOffsetOk labs ffis pos (aux.reverse++lines) → linesOffsetOk labs ffis pos (padSection nop lines aux) :=
  linesOffsetOk_padSection nop lines aux labs ffis pos

def runChecks : IO Bool := do
  IO.println "PASS full section padding offset preservation (12 original observations, all5guards, masked head/empty cases, counterexamples, all7opcodes and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetOffsetPaddingParity
