import Flapjack.Compiler.Backend.WordToStack.ProductionSelectorDomain

namespace Flapjack.Test.WordToStackSelectorDomainParity
open Flapjack Flapjack.RiscV

-- Compare complete same-input output trees with original inst_select at
-- riscv_config/temp23, including the executed positive-offset Store repair.
private def rows : List Bool :=
  [match wordInstSelectProgram 23 (.skip : WordProg (BitVec 64)) with
   | .skip => true | _ => false,
   match wordInstSelectProgram 23 (.seq (.assign 2 (.const 7)) .tick : WordProg (BitVec 64)) with
   | .seq (.inst (.const 2 7)) .tick => true | _ => false,
   match wordInstSelectProgram 23 (.set (.temp 1) (.var 18) : WordProg (BitVec 64)) with
   | .seq (.move 0 [(23,18)]) (.set (.temp 1) (.var 23)) => true | _ => false,
   match wordInstSelectProgram 23 (.assign 2 (.load (.var 18)) : WordProg (BitVec 64)) with
   | .seq (.move 0 [(23,18)]) (.inst (.mem .load 2 23)) => true | _ => false,
   match wordInstSelectProgram 23 (.store (.var 18) 10 : WordProg (BitVec 64)) with
   | .seq (.move 0 [(23,18)]) (.inst (.mem .store 10 23)) => true | _ => false,
   match wordInstSelectProgram 23 (.store (.op .add [.var 18,.const 7]) 10 : WordProg (BitVec 64)) with
   | .seq (.move 0 [(23,18)]) (.inst (.memOffset .store 10 23 7)) => true | _ => false,
   match wordInstSelectProgram 23 (.shareInst .store8 10 (.op .add [.var 18,.const 7]) : WordProg (BitVec 64)) with
   | .seq (.move 0 [(23,18)]) (.shareInst .store8 10 (.op .add [.var 23,.const 7])) => true | _ => false,
   match wordInstSelectProgram 23 (.ite .equal 1 (.imm 0) (.assign 2 (.const 7)) .tick : WordProg (BitVec 64)) with
   | .ite .equal 1 (.imm 0) (.inst (.const 2 7)) .tick => true | _ => false,
   match wordInstSelectProgram 23 (.loop [] (.assign 2 (.const 7)) [] : WordProg (BitVec 64)) with
   | .loop [] (.inst (.const 2 7)) [] => true | _ => false,
   match wordInstSelectProgram 23 (.mustTerminate (.assign 2 (.const 7)) : WordProg (BitVec 64)) with
   | .mustTerminate (.inst (.const 2 7)) => true | _ => false,
   match wordInstSelectProgram 23 (.call none (some 7) [] (some (1,.assign 3 (.const 9),5,6)) : WordProg (BitVec 64)) with
   | .call none (some 7) [] (some (1,.inst (.const 3 9),5,6)) => true | _ => false,
   match wordInstSelectProgram 23 (.call (some ([],([],[]),.assign 2 (.const 7),3,4)) (some 7) [] none : WordProg (BitVec 64)) with
   | .call (some ([],([],[]),.inst (.const 2 7),3,4)) (some 7) [] none => true | _ => false,
   match wordInstSelectProgram 23 (.call (some ([],([],[]),.seq (.assign 2 (.const 7)) .tick,3,4)) (some 7) []
      (some (1,.seq (.assign 3 (.const 9)) .tick,5,6)) : WordProg (BitVec 64)) with
   | .call (some ([],([],[]),.seq (.inst (.const 2 7)) .tick,3,4)) (some 7) []
      (some (1,.seq (.inst (.const 3 9)) .tick,5,6)) => true | _ => false]

example : rows = [true,true,true,true,true,true,true,true,true,true,true,true,true] := by
  simp only [rows, wordInstSelectProgram, wordInstSelectStoreCake, wordInstSelectAddressAtom,
    wordDeadSelectSeq]
  decide +kernel

-- The executed Store now has the original selected memory-instruction tree.
example : (match wordInstSelectProgram 23
    (.store (.op .add [.var 18,.const 7]) 10 : WordProg (BitVec 64)) with
    | .seq (.move 0 [(23,18)]) (.inst (.memOffset .store 10 23 7)) => true
    | _ => false) = true := by
  simp only [wordInstSelectProgram, wordInstSelectStoreCake, wordInstSelectAddressAtom,
    wordDeadSelectSeq]
  decide +kernel

private def fiveCarry : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))
example : [(wordLangProgToHOL (wordInstSelectProgramFrom fiveCarry)).isSome,
    (wordLangProgToHOL (wordInstSelectProgramFrom (.seq .tick fiveCarry))).isSome,
    (wordLangProgToHOL (wordInstSelectProgramFrom (.loop [] fiveCarry []))).isSome,
    (wordLangProgToHOL (wordInstSelectProgramFrom (.call none (some 7) [] (some (1,fiveCarry,2,3))))).isSome,
    (wordLangProgToHOL (wordInstSelectProgramFrom (.call (some ([],([],[]),fiveCarry,2,3)) (some 7) [] none))).isSome,
    (wordLangProgToHOL (wordInstSelectProgramFrom (.inst (.arith (.cakeAddCarry 1 2 3 4)) : WordProg (BitVec 8)))).isSome] =
    [false,false,false,false,false,true] := by
  decide +kernel

example {width : Nat} [NeZero width] (temporary : Nat) (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordInstSelectProgram temporary program)).isSome = true := by
  rw [wordLangProgToHOL_wordInstSelectProgram_isSome]
  exact accepted
example (program : WordProg (BitVec 1)) :
    (wordLangProgToHOL (wordInstSelectProgram 18446744073709551616 program)).isSome =
      (wordLangProgToHOL program).isSome := wordLangProgToHOL_wordInstSelectProgram_isSome _ program
example (program : WordProg (BitVec 80)) :
    (wordLangProgToHOL (wordInstSelectProgramFrom program)).isSome =
      (wordLangProgToHOL program).isSome := wordLangProgToHOL_wordInstSelectProgramFrom_isSome program

end Flapjack.Test.WordToStackSelectorDomainParity
