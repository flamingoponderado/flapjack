import Flapjack.RiscV.WordFuseConditions

/-! Complete original compile_exp output trees and helper boundaries from
word_simp_duplicate_if_source_probe.out. Expected trees are independent
transcriptions of original HOL outputs, not another Lean implementation. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Flapjack.Test.WordSimpDuplicateIfParity
open Flapjack RiscV
private def input : WordProg (BitVec 64) :=
  .seq (.ite .less 1 (.reg 2) (.assign 3 (.const 1)) (.assign 3 (.const 0)))
    (.seq (.assign 4 (.var 3)) (.ite .notEqual 4 (.imm 0) (.assign 5 (.const 7)) .skip))
private def originalTree : WordProg (BitVec 64) → Bool
  | .ite .less 1 (.reg 2)
      (.seq (.seq (.assign 3 (.const 1)) (.assign 4 (.const 1))) (.assign 5 (.const 7)))
      (.seq (.assign 3 (.const 0)) (.assign 4 (.const 0))) => true
  | _ => false
private def rows : List Bool :=
  [originalTree (wordToWordPreSsa input),
   match wordToWordPreSsa (.mustTerminate input) with
   | .mustTerminate body => originalTree body | _ => false,
   match wordToWordPreSsa (.loop [] input []) with
   | .loop [] body [] => originalTree body | _ => false,
   match wordToWordPreSsa (.call (some ([],([],[]),input,3,4)) (some 7) [1] none) with
   | .call (some ([],([],[]),body,3,4)) (some 7) [1] none => originalTree body | _ => false,
   match wordToWordPreSsa (.call none (some 7) [1] (some (1,input,3,4))) with
   | .call none (some 7) [1] (some (1,body,3,4)) => originalTree body | _ => false,
   match wordToWordPreSsa (.call (some ([],([],[]),input,3,4)) (some 7) [1] (some (1,input,5,6))) with
   | .call (some ([],([],[]),body,3,4)) (some 7) [1] (some (1,handler,5,6)) =>
       originalTree body && originalTree handler | _ => false,
   match wordToWordPreSsa (.ite .equal 8 (.imm 0) input .tick) with
   | .ite .equal 8 (.imm 0) body .tick => originalTree body | _ => false,
   match wordSimpDuplicateIf (.seq .tick .skip : WordProg (BitVec 64)) with
   | .seq .tick .skip => true | _ => false,
   (wordTryIfHoist2 0 input .skip .tick .skip).isNone,
   !(wordConditionPrefixSafe (.store (.var 1) 2 : WordProg (BitVec 64))),
   wordConditionPrefixSafe (.move 0 [(1,2)] : WordProg (BitVec 64)),
   wordDestRaise (.tick : WordProg (BitVec 64)) == 0,
   wordDestRaise (.raise 0 : WordProg (BitVec 64)) == 0,
   wordDestRaise (.raise 3 : WordProg (BitVec 64)) == 3]
example : rows = List.replicate 14 true := by decide +kernel
end Flapjack.Test.WordSimpDuplicateIfParity
