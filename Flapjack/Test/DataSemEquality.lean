module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Equality

@[expose] public section

/-! Regression cases for data-language equality. -/
namespace Flapjack.Test.DataSemEquality
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

private def refs : Spt (BvlSem.Ref Unit) :=
  sptInsert 0 (.byteArray true [1, 2]) <|
  sptInsert 1 (.byteArray true [1, 2]) <|
  sptInsert 2 (.byteArray false [1, 2]) .ln

example : doEq refs (.refPtr true 0) (.refPtr true 1) = .val true := by
  simp [doEq, refs, sptInsert, sptLookup]

example : doEq refs (.refPtr true 0) (.refPtr true 2) = .typeError := by
  simp [doEq, refs, sptInsert, sptLookup]

example : doEq refs (.refPtr false 0) (.refPtr true 0) = .typeError := by
  simp [doEq]

example : doEq refs (.block 3 5 [.number 7]) (.block 9 5 [.number 7]) = .val true := by
  simp [doEq, doEqList, isClosure]

example : doEq refs (.block 0 30 [.number 0]) (.block 0 31 [.number 1]) = .val true := by
  simp [doEq, isClosure]

example : doEqList refs [.number 1, .codePtr 0] [.number 2, .codePtr 0] = .val false := by
  simp [doEqList, doEq]

end Flapjack.Test.DataSemEquality
