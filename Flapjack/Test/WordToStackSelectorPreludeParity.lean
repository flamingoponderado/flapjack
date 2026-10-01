import Flapjack.Compiler.Backend.WordToStack.ProductionSelectorPrelude

namespace Flapjack.Test.WordToStackSelectorPreludeParity
open Flapjack Flapjack.RiscV

-- Same-input full-tree comparison with original inst_select_exp, using
-- riscv_config and tar=temp=23. All ten complete trees agree, including
-- the right-associated large-offset materialization nested under Load.
private def rows : List Bool :=
  [match (wordInstSelectAtom 23 (.const 7 : WordExp (BitVec 64))).1 with
   | .inst (.const 23 7) => true | _ => false,
   match (wordInstSelectAtom 23 (.var 18 : WordExp (BitVec 64))).1 with
   | .move 0 [(23,18)] => true | _ => false,
   match (wordInstSelectAtom 23 (.lookup .currHeap : WordExp (BitVec 64))).1 with
   | .get 23 .currHeap => true | _ => false,
   match (wordInstSelectAtom 23 (.load (.var 18) : WordExp (BitVec 64))).1 with
   | .seq (.move 0 [(23,18)]) (.inst (.mem .load 23 23)) => true | _ => false,
   match (wordInstSelectAtom 23 (.op .add [.var 18,.const 7] : WordExp (BitVec 64))).1 with
   | .seq (.move 0 [(23,18)]) (.inst (.arith (.binOp .add 23 23 (.imm 7)))) => true | _ => false,
   match (wordInstSelectAtom 23 (.shift .lsl (.var 18) (.const 3) : WordExp (BitVec 64))).1 with
   | .seq (.move 0 [(23,18)]) (.inst (.arith (.shift .lsl 23 23 (.imm 3)))) => true | _ => false,
   match (wordInstSelectAtom 23 (.shift .lsl (.var 18) (.const 64) : WordExp (BitVec 64))).1 with
   | .inst (.const 23 0) => true | _ => false,
   match (wordInstSelectAtom 23 (.op .xor [.lookup .currHeap,.const 7] : WordExp (BitVec 64))).1 with
   | .seq (.inst (.const 23 7)) (.opCurrHeap .xor 23 23) => true | _ => false,
   match (wordInstSelectAtom 23 (.load (.op .add [.var 18,.const 7]) : WordExp (BitVec 64))).1 with
   | .seq (.move 0 [(23,18)]) (.inst (.memOffset .load 23 23 7)) => true | _ => false,
   match (wordInstSelectAtom 23 (.load (.op .add [.var 18,.const 4096]) : WordExp (BitVec 64))).1 with
   | .seq (.seq (.move 0 [(23,18)])
       (.seq (.inst (.const 24 4096)) (.inst (.arith (.binOp .add 23 23 (.reg 24))))))
       (.inst (.mem .load 23 23)) => true | _ => false]

example : rows = [true,true,true,true,true,true,true,true,true,true] := by
  simp only [rows, wordInstSelectAtom, wordInstSelectLoadTail, wordDeadSelectSeq]
  decide +kernel

-- Reject the former production counter-tree; the original oracle is unchanged.
private def largeOffsetProduction : Bool :=
  match (wordInstSelectAtom 23
      (.load (.op .add [.var 18,.const 4096]) : WordExp (BitVec 64))).1 with
  | .seq (.seq (.seq (.move 0 [(23,18)]) (.inst (.const 24 4096)))
      (.inst (.arith (.binOp .add 23 23 (.reg 24))))) (.inst (.mem .load 23 23)) => true
  | _ => false
example : largeOffsetProduction = false := by
  simp only [largeOffsetProduction, wordInstSelectAtom, wordInstSelectLoadTail, wordDeadSelectSeq]
  decide +kernel

-- Full arbitrary expressions/temporaries, including natural register names
-- larger than the word width, are covered by the actual unconditional proofs.
example {width : Nat} [NeZero width] (temporary : Nat) (expression : WordExp (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectAtom temporary expression).1).isSome = true :=
  wordLangProgToHOL_wordInstSelectAtom_isSome temporary expression
example (expression : WordExp (BitVec 1)) :
    (wordLangProgToHOL (wordInstSelectAddressAtom 18446744073709551616 expression).1).isSome = true :=
  wordLangProgToHOL_wordInstSelectAddressAtom_isSome _ expression
example (expression : WordExp (BitVec 80)) :
    (wordLangProgToHOL (wordInstSelectAtom 1208925819614629174706176 expression).1).isSome = true :=
  wordLangProgToHOL_wordInstSelectAtom_isSome _ expression

-- Load-tail closure preserves incoming rejection rather than inventing support.
example : (wordLangProgToHOL (wordInstSelectLoadTail 23
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) (.var 18)).1).isSome = false := by
  decide +kernel

end Flapjack.Test.WordToStackSelectorPreludeParity
