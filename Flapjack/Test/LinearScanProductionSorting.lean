import Flapjack.Compiler.Backend.LinearScan.ProductionSorting

/-! Executable coverage for register and move sorting and bounds failures. -/
namespace Flapjack.Test.LinearScanProductionSorting

open Flapjack.LinearScan Flapjack.RegAlloc
open Flapjack.Translator.Monadic.MonadBase

private def initial : ProductionState :=
  ⟨#[0, 0, 0, 0], #[-3, 0, -3, 2], #[1, 1, 1, 1], #[2, 0, 3, 1],
    #[(3, (0, 1)), (1, (2, 3)), (2, (4, 5))]⟩

#guard
    let (result, state) := Production.sortRegs 0 4 initial
    (result, state.sorted_regs.toList) = (.success (), [0, 2, 1, 3])

#guard
    let (result, state) := Production.sortMoves 0 3 initial
    (result, state.sorted_moves.toList) =
      (.success (), [(1, (2, 3)), (2, (4, 5)), (3, (0, 1))])

#guard (Production.sortMoves 0 4 initial).1 = .failure .Subscript

#guard (Production.sortRegs 0 5 initial).1 = .failure .Subscript

end Flapjack.Test.LinearScanProductionSorting
