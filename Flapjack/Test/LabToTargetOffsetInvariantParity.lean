import Flapjack.Compiler.Backend.LabToTarget.OffsetInvariant
namespace Flapjack.Test.LabToTargetOffsetInvariantParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def ffis : List HolFfiName := [.extCall (.implode [97]),.extCall (.implode []),.extCall (.implode [])]
private def l1 : List (LabLineHOL 8) := [.label 1 2 3,.asm (.asmi (.inst .skip)) [] 2]
private def l2 : List (LabLineHOL 8) := [.labAsm (.jump (.lab 3 4)) 5 [] 3]
example : lineOffsetOk (width := 8) labs ffis 5 (.label 1 2 999) := True.intro
example : lineOffsetOk (width := 8) labs ffis 5 (.asm (.asmi (.inst .skip)) [] 999) := True.intro
example : ∀ l ∈ ([.labAsm (.jump (.lab 3 4)) 5 [] 99,
    .labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 3 4)) 5 [7] 99,
    .labAsm (.locValue 2 (.lab 3 4)) 5 [] 0,.labAsm (.call (.lab 3 4)) 5 [] 999,
    .labAsm (.callFFI (.implode [])) 187 [] 0,.labAsm .install 219 [] 0,
    .labAsm .halt 235 [] 0] : List (LabLineHOL 8)),lineOffsetOk labs ffis 5 l := by
  simp [lineOffsetOk]
  all_goals decide +kernel
example : ¬lineOffsetOk (width := 8) labs ffis 5 (.labAsm (.jump (.lab 3 4)) 99 [5] 1) := by
  simp only [lineOffsetOk]
  all_goals decide +kernel
example : lineOffsetOk (width := 8) .ln ffis 5 (.labAsm (.jump (.lab 3 4)) 251 [] 99) := by
  simp only [lineOffsetOk]
  all_goals decide +kernel
example : lineOffsetOk (width := 8) labs [] 5 (.labAsm (.callFFI (.implode [])) 203 [] 99) := by
  simp only [lineOffsetOk]
  all_goals decide +kernel
example : linesOffsetOk labs ffis 0 (l1++l2) ∧ linesOffsetOk labs ffis 0 l1 ∧
    linesOffsetOk labs ffis (0+(l1.map lineLen).sum) l2 := by
  have hp : linesOffsetOk labs ffis 0 l1 ∧ linesOffsetOk labs ffis (0+(l1.map lineLen).sum) l2 := by
    simp only [linesOffsetOk,lineOffsetOk,l1,l2]
    all_goals decide +kernel
  exact ⟨(linesOffsetOk_append labs ffis 0 l1 l2).2 hp,hp⟩
example : ¬linesOffsetOk labs ffis 0 l2 := by
  simp only [linesOffsetOk,lineOffsetOk,l2]
  all_goals decide +kernel
example : offsetOk labs ffis 0 [⟨7,l1⟩,⟨8,l2⟩,⟨9,[]⟩] := by
  simp only [offsetOk,linesOffsetOk,lineOffsetOk,l1,l2]
  all_goals decide +kernel
example : ¬offsetOk labs ffis 0 [⟨7,l1⟩,⟨8,[.labAsm (.jump (.lab 3 4)) 10 [] 3]⟩] := by
  simp only [offsetOk,linesOffsetOk,lineOffsetOk,l1]
  all_goals decide +kernel
example : linesOffsetOk (width := 1) .ln [] 17 [] ∧ offsetOk (width := 1) .ln [] 17 [⟨7,[]⟩,⟨8,[]⟩] ∧
    lineOffsetOk (width := 1) .ln [] 0 (.labAsm .halt 0 [] 99) := by
  simp only [linesOffsetOk,offsetOk,lineOffsetOk]
  all_goals decide +kernel
example : lineOffsetOk (width := 80) .ln [] (2^80+1)
    (.labAsm .halt (BitVec.ofNat 80 (2^80-17)) [7] 99) ∧
    ¬lineOffsetOk (width := 80) .ln [] (2^80+1) (.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 99) := by
  simp only [lineOffsetOk]
  all_goals decide +kernel
example {width : Nat} [NeZero width] (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (l1 l2 : List (LabLineHOL width)) :
    linesOffsetOk labs ffis pos (l1++l2) ↔ linesOffsetOk labs ffis pos l1 ∧
    linesOffsetOk labs ffis (pos+(l1.map lineLen).sum) l2 := linesOffsetOk_append labs ffis pos l1 l2

def runChecks : IO Bool := do
  IO.println "PASS full offset predicates/append (12 original observations, all7 labelled opcodes, lookup defaults/duplicates, stored-word mismatches, annotation positions and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetOffsetInvariantParity
