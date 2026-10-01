import Flapjack.Compiler.Backend.WordToStack.ProductionConstantDomain

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Flapjack.Test.WordToStackConstantDomainParity
open Flapjack RiscV

private def cs : NatInfoMap (BitVec 64) := [(1,7),(2,9)]

-- Full original program outputs, with the real wrapper's preceding Seq_assoc.
-- The last row retains the formerly failing input and original Tick oracle,
-- now matched by the repaired production wrapper (flapjack-2uae).
private def rows : List Bool :=
  [match wordConstFp (.skip : WordProg (BitVec 64)) with
   | .skip => true | _ => false,
   match wordConstFp (.seq (.assign 2 (.const 7)) (.assign 3 (.var 2)) : WordProg (BitVec 64)) with
   | .seq (.assign 2 (.const 7)) (.assign 3 (.const 7)) => true | _ => false,
   match wordConstFp (.seq (.assign 1 (.const 0))
       (.ite .equal 1 (.imm 0) (.assign 2 (.const 7)) (.assign 3 (.const 9))) : WordProg (BitVec 64)) with
   | .seq (.assign 1 (.const 0)) (.assign 2 (.const 7)) => true | _ => false,
   match wordConstFp (.ite .equal 1 (.imm 0) (.assign 2 (.const 7)) .tick : WordProg (BitVec 64)) with
   | .ite .equal 1 (.imm 0) (.assign 2 (.const 7)) .tick => true | _ => false,
   match (wordConstFpLoop (.call none (some 7) [1,2] (some (1,.assign 3 (.var 1),5,6))) cs).1 with
   | .seq (.seq (.assign 2 (.const 9)) (.assign 1 (.const 7)))
       (.call none (some 7) [1,2] (some (1,.assign 3 (.var 1),5,6))) => true | _ => false,
   match (wordConstFpLoop (.call (some ([],([],[]),.seq (.assign 3 (.var 1)) .tick,3,4))
       (some 7) [1] none) cs).1 with
   | .seq (.assign 1 (.const 7)) (.call (some ([],([],[]),.seq (.assign 3 (.var 1)) .tick,3,4))
       (some 7) [1] none) => true | _ => false,
   match (wordConstFpLoop (.call (some ([],([],[]),.assign 3 (.var 1),3,4))
       (some 7) [1] (some (1,.assign 4 (.var 2),5,6))) cs).1 with
   | .seq (.assign 1 (.const 7)) (.call (some ([],([],[]),.assign 3 (.var 1),3,4))
       (some 7) [1] (some (1,.assign 4 (.var 2),5,6))) => true | _ => false,
   match (wordConstFpLoop (.alloc 1 ([],[])) cs).1 with
   | .seq (.assign 1 (.const 7)) (.alloc 1 ([],[])) => true | _ => false,
   match (wordConstFpLoop (.install 1 2 3 4 ([],[])) cs).1 with
   | .seq (.seq (.assign 2 (.const 9)) (.assign 1 (.const 7)))
       (.install 1 2 3 4 ([],[])) => true | _ => false,
   match (wordConstFpLoop (.ffi "echo" 1 2 3 4 ([],[])) cs).1 with
   | .seq (.seq (.assign 2 (.const 9)) (.assign 1 (.const 7)))
       (.ffi "echo" 1 2 3 4 ([],[])) => true | _ => false,
   match (wordConstFpLoop (.loop [] (.assign 3 (.var 1)) []) cs).1 with
   | .loop [] (.assign 3 (.var 1)) [] => true | _ => false,
   match (wordConstFpLoop (.mustTerminate (.assign 3 (.var 1))) cs).1 with
   | .mustTerminate (.assign 3 (.const 7)) => true | _ => false,
   match wordConstFp (.seq .tick .skip : WordProg (BitVec 64)) with
   | .tick => true | _ => false]

example : rows = [true,true,true,true,true,true,true,true,true,true,true,true,true] := by
  decide +kernel

example : wordConstFp (.seq .tick .skip : WordProg (BitVec 64)) = .tick := by
  simp [wordConstFp, wordSimpSeqAssoc, wordSimpSeqAssocAcc,
    wordSimpSmartSeq, wordConstFpLoop]

private def rejected : WordProg (BitVec 64) := .inst (.arith (.addCarry 1 2 3 4 5))
private def discarded : WordProg (BitVec 64) :=
  .seq (.assign 1 (.const 0)) (.ite .equal 1 (.imm 0) .tick rejected)

-- Constant branch removal can eliminate a rejected primitive: only the source
-- acceptance implication is valid universally, not domain equality.
example : (wordLangProgToHOL discarded).isSome = false ∧
    (wordLangProgToHOL (wordConstFp discarded)).isSome = true := by decide +kernel

example : (wordLangProgToHOL (wordConstFp rejected)).isSome = false := by decide +kernel
example : (wordLangProgToHOL (wordConstFp (.loop [] rejected []))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (wordConstFp
    (.call none (some 7) [] (some (1,rejected,3,4))))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (wordConstFp
    (.call (some ([],([],[]),rejected,3,4)) (some 7) [] none))).isSome = false := by decide +kernel

example (p : WordProg (BitVec 1)) (h : (wordLangProgToHOL p).isSome = true) :
    (wordLangProgToHOL (wordConstFp p)).isSome = true := wordLangProgToHOL_wordConstFp_isSome p h
example (p : WordProg (BitVec 80)) (h : (wordLangProgToHOL p).isSome = true) :
    (wordLangProgToHOL (wordConstFp p)).isSome = true := wordLangProgToHOL_wordConstFp_isSome p h

def runChecks : IO Bool := do
  IO.println "PASS actual constant-pass codec closure (13 original trees; trailing Skip repaired)"
  pure true

end Flapjack.Test.WordToStackConstantDomainParity
