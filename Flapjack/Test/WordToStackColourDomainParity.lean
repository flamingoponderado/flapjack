import Flapjack.Compiler.Backend.WordToStack.ProductionColourDomain

/-! Kernel replay of fresh original colouring equations, plus full-domain
and guard sentinels. HOL has no production memory guard or five-register
AddCarry; those Flapjack-only boundaries are tested explicitly. -/
namespace Flapjack.Test.WordToStackColourDomainParity
open Flapjack

private def colour (name : Nat) := name + 10
private abbrev load16 : WordProg (BitVec 8) := .inst (.memOffset .load16 3 5 7)
private abbrev store16 : WordProg (BitVec 8) := .inst (.memOffset .store16 3 5 7)

example : wordApplyColour colour load16 = load16 := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour store16 = store16 := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.inst (.memOffset .load8 3 5 7) : WordProg (BitVec 8)) =
    .inst (.memOffset .load8 13 15 7) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.inst (.memOffset .store32 3 5 7) : WordProg (BitVec 8)) =
    .inst (.memOffset .store32 13 15 7) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.inst (.arith (.cakeAddCarry 1 2 3 4)) : WordProg (BitVec 8)) =
    .inst (.arith (.cakeAddCarry 11 12 13 14)) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour (fun _ => 0) (.inst (.const 3 7) : WordProg (BitVec 8)) =
    .inst (.const 0 7) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.seq (.inst (.const 3 7)) (.raise 5) : WordProg (BitVec 8)) =
    .seq (.inst (.const 13 7)) (.raise 15) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.mustTerminate load16) = .mustTerminate load16 := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.ite .equal 3 (.reg 5) load16 (.inst (.const 2 7))) =
    .ite .equal 13 (.reg 15) load16 (.inst (.const 12 7)) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.loop [] load16 []) = .loop [] load16 [] := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour (.call none none [3] (some (5, load16, 7, 9))) =
    .call none none [13] (some (15, load16, 7, 9)) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour colour
    (.call (some ([3], ([], []), .inst (.const 2 7), 19, 23)) (some 17) [5]
      (some (7, store16, 29, 31))) =
    .call (some ([13], ([], []), .inst (.const 12 7), 19, 23)) (some 17) [15]
      (some (17, store16, 29, 31)) := by simp only [wordApplyColour] <;> rfl
example : wordApplyColour (fun name => 1208925819614629174706176 + name)
    (.inst (.const 3 7) : WordProg (BitVec 8)) =
    .inst (.const 1208925819614629174706179 7) := by simp only [wordApplyColour] <;> rfl

private def fiveCarry : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))
private def domains : List (WordProg (BitVec 8)) :=
  [.skip, load16, store16, fiveCarry,
   .call none none [] (some (1, fiveCarry, 2, 3)),
   .call (some ([], ([], []), fiveCarry, 2, 3)) none [] none,
   .call none none [] (some (1, load16, 2, 3)),
   .seq .skip (.loop [] (.mustTerminate fiveCarry) []),
   .ite .equal 1 (.imm 0) (.inst (.const 2 7)) (.raise 3)]

example : domains.map (fun program => (wordLangProgToHOL program).isSome) =
    [true,true,true,false,false,false,true,false,true] := by decide +kernel
example : domains.map (fun program => (wordLangProgToHOL (wordApplyColour (fun _ => 0) program)).isSome) =
    [true,true,true,false,false,false,true,false,true] := by
  simp only [wordLangProgToHOL_wordApplyColour_isSome]
  decide +kernel
example : domains.map RiscV.allocatorMemorySupported =
    [true,false,false,true,true,true,false,true,true] := by
  simp [domains, fiveCarry, load16, store16, RiscV.allocatorMemorySupported]
example : domains.map (fun program => RiscV.allocatorMemorySupported (wordApplyColour (fun _ => 0) program)) =
    [true,false,false,true,true,true,false,true,true] := by
  simp only [allocatorMemorySupported_wordApplyColour]
  simp [domains, fiveCarry, load16, store16, RiscV.allocatorMemorySupported]

example {α : Type u} (colour : Nat → Nat) (program : WordProg α) :
    RiscV.allocatorMemorySupported (wordApplyColour colour program) =
      RiscV.allocatorMemorySupported program := allocatorMemorySupported_wordApplyColour colour program
example {width : Nat} (colour : Nat → Nat) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordApplyColour colour program)).isSome =
      (wordLangProgToHOL program).isSome := wordLangProgToHOL_wordApplyColour_isSome colour program

end Flapjack.Test.WordToStackColourDomainParity
