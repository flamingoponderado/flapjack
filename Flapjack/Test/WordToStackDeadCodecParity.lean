import Flapjack.Compiler.Backend.WordToStack.ProductionDeadCodecDomain

/-! Same-input kernel replay of fresh original complete dead-code output trees. -/
namespace Flapjack.Test.WordToStackDeadCodecParity
open Flapjack Flapjack.RiscV

private def rows : List Bool :=
  [match wordRemoveDeadProgram (.skip : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordRemoveDeadProgram (.move 1 [(1,2)] : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordRemoveDeadProgram (.inst (.const 1 7) : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordRemoveDeadProgram (.inst (.memOffset .load 1 2 7) : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordRemoveDeadProgram (.inst (.memOffset .load16 1 2 7) : WordProg (BitVec 8)) with
   | .inst (.memOffset .load16 1 2 7) => true
   | _ => false,
   match wordRemoveDeadProgram (.inst (.memOffset .store 1 2 7) : WordProg (BitVec 8)) with
   | .inst (.memOffset .store 1 2 7) => true
   | _ => false,
   match wordRemoveDeadProgram (.shareInst .load 1 (.var 2) : WordProg (BitVec 8)) with
   | .shareInst .load 1 (.var 2) => true
   | _ => false,
   match wordRemoveDeadProgram (.seq (.inst (.const 1 7)) (.inst (.memOffset .store 2 3 0)) : WordProg (BitVec 8)) with
   | .inst (.memOffset .store 2 3 0) => true
   | _ => false,
   match wordRemoveDeadProgram (.ite .equal 1 (.imm 0) (.inst (.const 2 7)) .skip : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordRemoveDeadProgram (.loop [] (.inst (.const 1 7)) [] : WordProg (BitVec 8)) with
   | .loop [] .skip [] => true
   | _ => false,
   match wordRemoveDeadProgram (.mustTerminate (.inst (.const 1 7)) : WordProg (BitVec 8)) with
   | .mustTerminate .skip => true
   | _ => false,
   match wordRemoveDeadProgram (.call none (some 7) [] (some (1,.inst (.const 2 7),3,4)) : WordProg (BitVec 8)) with
   | .call none (some 7) [] (some (1,.inst (.const 2 7),3,4)) => true
   | _ => false,
   match wordRemoveDeadProgram (.call (some ([],([],[]),.inst (.const 2 7),3,4)) (some 7) [] (some (1,.inst (.const 5 7),6,7)) : WordProg (BitVec 8)) with
   | .call (some ([],([],[]),.skip,3,4)) (some 7) [] (some (1,.skip,6,7)) => true
   | _ => false]

example : rows = List.replicate 13 true := by
  simp only [rows, wordRemoveDeadProgram, wordDeadCodeWithStores,
    wordDeadMove, wordDeadInst, WordAlloc.removeDeadInstExecutable,
    WordAlloc.removeDeadInstCore, WordAlloc.numSetToExact]
  decide +kernel

private def fiveCarry : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))

-- The production-only primitive has no HOL constructor. Its real deletion
-- boundary demonstrates why codec closure must not assert domain equality.
example : [(wordLangProgToHOL fiveCarry).isSome,
    (wordLangProgToHOL (wordRemoveDeadProgram fiveCarry)).isSome,
    (wordLangProgToHOL (wordDeadCodeWithStores fiveCarry [1] [] [] []).1).isSome,
    (wordLangProgToHOL (wordRemoveDeadProgram
      (.call none (some 7) [] (some (1,fiveCarry,2,3))))).isSome,
    (wordLangProgToHOL (wordRemoveDeadProgram
      (.call (some ([],([],[]),fiveCarry,2,3)) (some 7) [] none))).isSome] =
    [false,true,false,false,true] := by
  simp only [fiveCarry, wordRemoveDeadProgram, wordDeadCodeWithStores,
    wordDeadInst, WordAlloc.removeDeadInstExecutable, WordAlloc.numSetToExact]
  decide +kernel

example {width : Nat} (program : WordProg (BitVec width)) (live : List Nat)
    (frames : List (List Nat × List Nat)) (returnLabels nlive : List Nat)
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordDeadCodeWithStores program live frames returnLabels nlive).1).isSome = true :=
  wordLangProgToHOL_wordDeadCodeWithStores_isSome program live frames returnLabels nlive accepted

end Flapjack.Test.WordToStackDeadCodecParity
