import Flapjack.Compiler.Backend.WordToStack.ProductionCseCodecDomain

/-! Same-input kernel replay of fresh original complete CSE output trees. -/
namespace Flapjack.Test.WordToStackCseCodecParity
open Flapjack Flapjack.RiscV

private def rows : List Bool :=
  [match wordCseProp (.skip : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordCseProp (.move 1 [(1,3)] : WordProg (BitVec 8)) with
   | .move 1 [(1,3)] => true
   | _ => false,
   match wordCseProp (.seq (.inst (.const 1 7)) (.inst (.const 3 7)) : WordProg (BitVec 8)) with
   | .seq (.inst (.const 1 7)) (.inst (.const 3 7)) => true
   | _ => false,
   match wordCseProp (.seq (.get 1 .heapLength) (.get 3 .heapLength) : WordProg (BitVec 8)) with
   | .seq (.get 1 .heapLength) (.move 1 [(3,1)]) => true
   | _ => false,
   match wordCseProp (.seq (.inst (.memOffset .load 1 3 0)) (.inst (.memOffset .load 5 3 0)) : WordProg (BitVec 8)) with
   | .seq (.inst (.memOffset .load 1 3 0)) (.move 0 [(5,1)]) => true
   | _ => false,
   match wordCseProp (.seq (.inst (.memOffset .load8 1 3 7)) (.inst (.memOffset .load8 5 3 7)) : WordProg (BitVec 8)) with
   | .seq (.inst (.memOffset .load8 1 3 7)) (.move 0 [(5,1)]) => true
   | _ => false,
   match wordCseProp (.seq (.inst (.arith (.shift .lsl 1 3 (.imm 1)))) (.inst (.arith (.shift .lsl 5 3 (.imm 1)))) : WordProg (BitVec 8)) with
   | .seq (.inst (.arith (.shift .lsl 1 3 (.imm 1)))) (.move 0 [(5,1)]) => true
   | _ => false,
   match wordCseProp (.inst (.memOffset .load16 1 3 7) : WordProg (BitVec 8)) with
   | .inst (.memOffset .load16 1 3 7) => true
   | _ => false,
   match wordCseProp (.shareInst .load 1 (.var 3) : WordProg (BitVec 8)) with
   | .shareInst .load 1 (.var 3) => true
   | _ => false,
   match wordCseProp (.loop [] (.seq (.get 1 .heapLength) (.get 3 .heapLength)) [] : WordProg (BitVec 8)) with
   | .loop [] (.seq (.get 1 .heapLength) (.move 1 [(3,1)])) [] => true
   | _ => false,
   match wordCseProp (.mustTerminate (.seq (.get 1 .heapLength) (.get 3 .heapLength)) : WordProg (BitVec 8)) with
   | .mustTerminate (.seq (.get 1 .heapLength) (.move 1 [(3,1)])) => true
   | _ => false,
   match wordCseProp (.ite .equal 1 (.imm 0) (.seq (.get 3 .heapLength) (.get 5 .heapLength)) .skip : WordProg (BitVec 8)) with
   | .ite .equal 1 (.imm 0) (.seq (.get 3 .heapLength) (.move 1 [(5,3)])) .skip => true
   | _ => false,
   match wordCseProp (.call none (some 7) [] (some (1,.seq (.get 3 .heapLength) (.get 5 .heapLength),2,3)) : WordProg (BitVec 8)) with
   | .call none (some 7) [] (some (1,.seq (.get 3 .heapLength) (.get 5 .heapLength),2,3)) => true
   | _ => false,
   match wordCseProp (.call (some ([],([],[]),.seq (.get 3 .heapLength) (.get 5 .heapLength),2,3)) (some 7) [] (some (1,.inst (.const 5 7),4,5)) : WordProg (BitVec 8)) with
   | .call (some ([],([],[]),.seq (.get 3 .heapLength) (.get 5 .heapLength),2,3)) (some 7) [] (some (1,.inst (.const 5 7),4,5)) => true
   | _ => false,
   match wordCseProp (.seq (.inst (.memOffset .load 1 3 0)) (.seq (.inst (.memOffset .store 5 7 0)) (.inst (.memOffset .load 9 3 0))) : WordProg (BitVec 8)) with
   | .seq (.inst (.memOffset .load 1 3 0)) (.seq (.inst (.memOffset .store 5 7 0)) (.inst (.memOffset .load 9 3 0))) => true
   | _ => false,
   match wordCseProp (.seq (.get 1 .heapLength) (.seq (.call none (some 7) [] none) (.get 3 .heapLength)) : WordProg (BitVec 8)) with
   | .seq (.get 1 .heapLength) (.seq (.call none (some 7) [] none) (.get 3 .heapLength)) => true
   | _ => false]

example : rows = List.replicate 16 true := by
  simp only [rows, wordCseProp, wordCseProg, wordCseInst]
  decide +kernel

private def fiveCarry : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))
private def domains : List (WordProg (BitVec 8)) :=
  [.skip, .inst (.arith (.cakeAddCarry 1 2 3 4)), .inst (.memOffset .load16 1 3 7),
   fiveCarry, .seq .skip fiveCarry, .loop [] fiveCarry [],
   .call none (some 7) [] (some (1,fiveCarry,2,3)),
   .call (some ([],([],[]),fiveCarry,2,3)) (some 7) [] none]

example : domains.map (fun program => (wordLangProgToHOL (wordCseProp program)).isSome) =
    [true,true,true,false,false,false,false,false] := by
  simp only [wordLangProgToHOL_wordCseProp_isSome]
  decide +kernel

example {width : Nat} (data : WordCseKnowledge) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCseProg data program).1).isSome =
      (wordLangProgToHOL program).isSome :=
  wordLangProgToHOL_wordCseProg_isSome data program

end Flapjack.Test.WordToStackCseCodecParity
