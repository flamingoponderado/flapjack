module

public import Flapjack.Compiler.Backend.LinearScan.ProductionIntervals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Translator.Monadic.MonadBase
public meta import Flapjack.Compiler.Backend.LinearScan.HiddenState
public meta import Flapjack.Compiler.Backend.RegAlloc.ClashTree
public meta import Flapjack.Compiler.Backend.RegAlloc.Exceptions
public meta import Flapjack.Compiler.Backend.LinearScan.ProductionIntervals
@[expose] public section

/-! Executable checks of the array-backed interval traversal, including the
out-of-range behavior of the source monad. -/
namespace Flapjack.Test.LinearScanProductionIntervals

open Flapjack.LinearScan Flapjack.RegAlloc
open Flapjack.Translator.Monadic.MonadBase

private def initial : ProductionState :=
  ⟨#[0, 0], #[1, 1], #[1, 1], #[0, 0], #[]⟩

private def smallTree : ClashTree := .delta [1] [0]

#guard
    let (result, state) := Production.getIntervals smallTree initial
    (result, state.int_beg.toList, state.int_end.toList) =
      (.success (-3), [-2, 0], [-1, 0])

#guard
    let (result, state) := Production.getIntervals (.delta [2] []) initial
    (result, state.toSource) = (.failure .Subscript, initial.toSource)

#guard
    let (result, state) := Production.getIntervals (.delta [0, 2] []) initial
    (result, state.int_beg.toList, state.int_end.toList) =
      (.failure .Subscript, [0, 1], [1, 1])

end Flapjack.Test.LinearScanProductionIntervals
