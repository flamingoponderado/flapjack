import Flapjack.Compiler.Backend.WordToStack.ProductionUnreachCodecDomain

/-! Exact same-input kernel replay of fresh original unreachable output trees. -/
namespace Flapjack.Test.WordToStackUnreachCodecParity
open Flapjack Flapjack.RiscV

private def rows : List Bool :=
  [match wordRemoveUnreachableAfterCopy (.skip : WordProg (BitVec 8)) with
   | .skip => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq .skip .tick : WordProg (BitVec 8)) with
   | .tick => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.raise 1) (.inst (.const 2 7)) : WordProg (BitVec 8)) with
   | .raise 1 => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.return 1 [2]) .tick : WordProg (BitVec 8)) with
   | .return 1 [2] => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.break 0) .tick : WordProg (BitVec 8)) with
   | .break 0 => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.continue 0) .tick : WordProg (BitVec 8)) with
   | .continue 0 => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.call none (some 7) [] none) .tick : WordProg (BitVec 8)) with
   | .call none (some 7) [] none => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.move 1 [(1,2)]) (.move 0 [(3,1)]) : WordProg (BitVec 8)) with
   | .move 1 [(3,2),(1,2)] => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.move 0 [(1,2)]) (.move 1 [(1,3)]) : WordProg (BitVec 8)) with
   | .move 1 [(1,3)] => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.move 1 [(1,2)]) (.seq (.move 0 [(3,1)]) .tick) : WordProg (BitVec 8)) with
   | .seq (.move 1 [(3,2),(1,2)]) .tick => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.seq (.seq .tick .tick) .tick : WordProg (BitVec 8)) with
   | .seq .tick (.seq .tick .tick) => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.loop [] (.seq (.raise 1) .tick) [] : WordProg (BitVec 8)) with
   | .loop [] (.raise 1) [] => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.mustTerminate (.seq (.return 1 []) .tick) : WordProg (BitVec 8)) with
   | .mustTerminate (.return 1 []) => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.ite .equal 1 (.imm 0) (.seq (.raise 2) .tick) (.seq .skip .tick) : WordProg (BitVec 8)) with
   | .ite .equal 1 (.imm 0) (.raise 2) .tick => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.call none (some 7) [] (some (1,.seq (.raise 2) .tick,3,4)) : WordProg (BitVec 8)) with
   | .call none (some 7) [] (some (1,.seq (.raise 2) .tick,3,4)) => true
   | _ => false,
   match wordRemoveUnreachableAfterCopy (.call (some ([],([],[]),.seq (.raise 2) .tick,3,4)) (some 7) [] (some (1,.seq (.break 0) .tick,5,6)) : WordProg (BitVec 8)) with
   | .call (some ([],([],[]),.raise 2,3,4)) (some 7) [] (some (1,.break 0,5,6)) => true
   | _ => false]

example : rows = List.replicate 16 true := by
  simp only [rows, wordRemoveUnreachableAfterCopy, wordCopyUnreachParts,
    wordCopyUnreachPartsAcc, List.foldr, wordCopyUnreachSeq]
  decide +kernel

private def fiveCarry : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))

example : [(wordLangProgToHOL (.seq (.raise 1) fiveCarry)).isSome,
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy (.seq (.raise 1) fiveCarry))).isSome,
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy fiveCarry)).isSome,
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy
      (.call none (some 7) [] (some (1,.seq (.raise 1) fiveCarry,2,3))))).isSome,
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy
      (.call (some ([],([],[]),.seq (.raise 1) fiveCarry,2,3)) (some 7) [] none))).isSome] =
    [false,true,false,false,true] := by
  simp only [fiveCarry, wordRemoveUnreachableAfterCopy, wordCopyUnreachParts,
    wordCopyUnreachPartsAcc, List.foldr, wordCopyUnreachSeq]
  decide +kernel

example {width : Nat} (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy program)).isSome = true :=
  wordLangProgToHOL_wordRemoveUnreachableAfterCopy_isSome program accepted

end Flapjack.Test.WordToStackUnreachCodecParity
