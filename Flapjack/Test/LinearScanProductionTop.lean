module

public import Flapjack.Compiler.Backend.LinearScan.ProductionTopLevel

-- Checks below run compiled code from these modules.
public meta import Flapjack.Misc.Sptree
public meta import Flapjack.Translator.Monadic.MonadBase
public meta import Flapjack.Compiler.Backend.RegAlloc.ClashTree
public meta import Flapjack.Compiler.Backend.RegAlloc.Exceptions
public meta import Flapjack.Compiler.Backend.LinearScan.ProductionTopLevel
@[expose] public section

/-! The array-backed allocator replays representative full outputs captured
from the original HOL allocator, including spills and physical registers. -/
namespace Flapjack.Test.LinearScanProductionTop

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
open Flapjack.LinearScan.Production

#guard linearScanRegAlloc 3 [] (.delta [1, 5] [2]) [] =
    .success (.bn (.ls 1) (.bs (.ls 0) 1 .ln))

#guard linearScanRegAlloc 2 [] (.delta [1, 5, 9] [3]) [(1, 5)] =
    .success (.bn .ln (.bs (.bs .ln 1 (.ls 2)) 0 (.ls 2)))

#guard linearScanRegAlloc 1 [] (.branch (some (sptInsert 1 () .ln)) (.delta [1] [5]) (.delta [9] [1])) [] =
    .success (.bn .ln (.bs (.bs .ln 0 (.ls 0)) 1 .ln))

#guard linearScanRegAlloc 2 [] (.delta [0, 2, 5] [4, 7]) [] =
    .success (.bs (.bs .ln 1 (.ls 2)) 0 (.bn (.ls 3) (.bn .ln (.ls 3))))

#guard linearScanRegAlloc 2 [(3, (5, 7))] (.seq (.delta [3, 5] [7, 1]) (.delta [7] [5])) [(5, 1)] =
    .success (.bn .ln (.bs (.ls 1) 0 (.bs .ln 3 (.ls 2))))

end Flapjack.Test.LinearScanProductionTop
