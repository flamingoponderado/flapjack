import Flapjack.RiscV.WordSimp

/-! Original HOL Seq_assoc clauses and whole output trees captured in
word_simp_seq_assoc_source_probe.out. The earlier alternate Lean traversal
retained trailing Skip and was not an original oracle. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Flapjack.Test.WordSimpSeqAssocParity
open Flapjack RiscV
private def s : WordProg (BitVec 64) := .skip
private def a : WordProg (BitVec 64) := .assign 1 (.const 7)
private def b : WordProg (BitVec 64) := .assign 2 (.const 9)
private def rows : List Bool :=
  [match wordSimpSeqAssocAcc s s with | .skip => true | _ => false,
   match wordSimpSeqAssocAcc a s with | .assign 1 (.const 7) => true | _ => false,
   match wordSimpSeqAssoc (.seq .tick s) with | .tick => true | _ => false,
   match wordSimpSeqAssoc (.seq (.seq .tick s) .tick) with | .seq .tick .tick => true | _ => false,
   match wordSimpSeqAssoc (.seq (.seq s s) (.seq s s)) with | .skip => true | _ => false,
   match wordSimpSeqAssoc (.seq a (.seq s b)) with
   | .seq (.assign 1 (.const 7)) (.assign 2 (.const 9)) => true | _ => false,
   match wordSimpSeqAssoc (.seq .tick (.seq (.raise 3) (.return 1 [2])) : WordProg (BitVec 64)) with
   | .seq (.seq .tick (.raise 3)) (.return 1 [2]) => true | _ => false,
   match wordSimpSeqAssoc (.ite .equal 1 (.imm 0) (.seq s .tick) (.seq (.raise 3) s)) with
   | .ite .equal 1 (.imm 0) .tick (.raise 3) => true | _ => false,
   match wordSimpSeqAssoc (.loop [] (.seq (.seq s .tick) s) []) with
   | .loop [] .tick [] => true | _ => false,
   match wordSimpSeqAssoc (.mustTerminate (.seq (.seq s .tick) s)) with
   | .mustTerminate .tick => true | _ => false,
   match wordSimpSeqAssoc (.call none (some 7) [1] (some (1,.seq .tick s,3,4))) with
   | .call none (some 7) [1] (some (1,.tick,3,4)) => true | _ => false,
   match wordSimpSeqAssoc (.call (some ([],([],[]),.seq s .tick,3,4)) (some 7) [1] none) with
   | .call (some ([],([],[]),.tick,3,4)) (some 7) [1] none => true | _ => false,
   match wordSimpSeqAssoc (.call (some ([],([],[]),.seq .tick s,3,4)) (some 7) [1]
       (some (1,.seq s (.seq (.raise 3) s),5,6))) with
   | .call (some ([],([],[]),.tick,3,4)) (some 7) [1] (some (1,.raise 3,5,6)) => true | _ => false,
   match wordSimpSeqAssocAcc (.seq .tick s) s with | .seq .tick .skip => true | _ => false,
   match wordSimpSeqAssoc (.inst (.const 2 9) : WordProg (BitVec 64)) with
   | .inst (.const 2 9) => true | _ => false]
example : rows = List.replicate 15 true := by decide +kernel
-- Same formerly failing input and original Tick output, now repaired.
example : wordSimpSeqAssoc (.seq .tick .skip : WordProg (BitVec 64)) = .tick := by
  simp [wordSimpSeqAssoc, wordSimpSeqAssocAcc, wordSimpSmartSeq]
example {α : Type u} (before : WordProg α) : wordSimpSeqAssocAcc before .skip = before := by
  simp [wordSimpSeqAssocAcc]
-- Store addresses remain for the subsequent instruction selector.
example : (match wordConstFp (.store (.op .add [.var 13,.const 8]) 10 : WordProg (BitVec 64)) with
    | .store (.op .add [.var 13,.const 8]) 10 => true | _ => false) = true := by decide +kernel
end Flapjack.Test.WordSimpSeqAssocParity
