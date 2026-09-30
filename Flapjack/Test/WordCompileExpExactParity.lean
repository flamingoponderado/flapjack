import Flapjack.Pancake.LoopToWord.WordCompileExpExact

/-! Focused production/exact-HOL expression compiler commutation fixtures. -/

namespace Flapjack.Test.WordCompileExpExactParity

open Flapjack

def duplicateContext : WordContext :=
  { vars := [(3, 8), (3, 9), (5, 12)] }

def emptyContext : WordContext := { vars := [] }

example : wordCompileExp duplicateContext (.var 3 : LoopExp (BitVec 8)) =
    some (.var 8) := by
  simp [wordCompileExp, wordFindVar, duplicateContext, lookupNatInfo]

example : wordCompileExp emptyContext (.var 4 : LoopExp (BitVec 8)) =
    some (.var 0) := by
  simp [wordCompileExp, wordFindVar, emptyContext, lookupNatInfo]

def nestedExpression : LoopExp (BitVec 8) :=
  .op .add [.var 3, .load (.shift .lsl (.var 5) (.const 1))]

def nestedExpected : WordExp (BitVec 8) :=
  .op .add [.var 8, .load (.shift .lsl (.var 12) (.const 1))]

example : wordCompileExp duplicateContext nestedExpression = some nestedExpected := by
  simp [wordCompileExp, wordCompileExp.wordCompileExpList,
    nestedExpression, nestedExpected, wordFindVar,
    duplicateContext, lookupNatInfo]

example : wordCompileExp duplicateContext nestedExpression = some (wordExpFromHOL
    (LoopToWord.compExpHOL (wordContextToHOLContext duplicateContext)
      (.op .add [.var 3, .load (.shift .lsl (.var 5) (.const 1))]))) := by
  have hdecode : executableLoopExpToHol nestedExpression =
      some (.op .add [.var 3, .load (.shift .lsl (.var 5) (.const 1))]) := by
    simp [nestedExpression, executableLoopExpToHol,
      executableLoopExpToHol.executableLoopExpListToHol]
  exact wordCompileExp_eq_compExpHOL_of_codec duplicateContext nestedExpression
    (.op .add [.var 3, .load (.shift .lsl (.var 5) (.const 1))]) hdecode

example : wordCompileExpThroughHOL duplicateContext nestedExpression =
    some nestedExpected := by
  simp [wordCompileExpThroughHOL, executableLoopExpToHol,
    executableLoopExpToHol.executableLoopExpListToHol,
    LoopToWord.compExpHOL, wordExpFromHOL,
    nestedExpression, nestedExpected, findVarHOL_wordFindVar,
    wordFindVar, duplicateContext, lookupNatInfo]

example {width : Nat} [NeZero width] (context : WordContext)
    (expression : LoopExp (BitVec width))
    (exactExpression : HolLoopExp width)
    (hdecode : executableLoopExpToHol expression = some exactExpression) :
    wordCompileExp context expression = some (wordExpFromHOL
      (LoopToWord.compExpHOL (wordContextToHOLContext context) exactExpression)) :=
  wordCompileExp_eq_compExpHOL_of_codec context expression exactExpression hdecode

example : wordCompileExp emptyContext
    (.cmp .equal (.var 4) (.const (1 : BitVec 8))) = none := by
  simp [wordCompileExp]

example : wordCompileExpThroughHOL emptyContext
    (.cmp .equal (.var 4) (.const (1 : BitVec 8))) = none := by
  simp [wordCompileExpThroughHOL]

def runChecks : IO Bool := do
  IO.println "PASS production wordCompileExp agrees with exact compExpHOL codec fixtures"
  return true

end Flapjack.Test.WordCompileExpExactParity
