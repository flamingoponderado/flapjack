import Flapjack.Compiler.Backend.LinearScan.ProductionTopLevel

/-! The array-backed allocator replays representative full outputs captured
from the original HOL allocator, including spills and physical registers. -/
namespace Flapjack.Test.LinearScanProductionTop

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
open Flapjack.LinearScan.Production

example : linearScanRegAlloc 3 [] (.delta [1, 5] [2]) [] =
    .success (.bn (.ls 1) (.bs (.ls 0) 1 .ln)) := by native_decide

example : linearScanRegAlloc 2 [] (.delta [1, 5, 9] [3]) [(1, 5)] =
    .success (.bn .ln (.bs (.bs .ln 1 (.ls 2)) 0 (.ls 2))) := by native_decide

example : linearScanRegAlloc 1 [] (.branch (some (sptInsert 1 () .ln)) (.delta [1] [5]) (.delta [9] [1])) [] =
    .success (.bn .ln (.bs (.bs .ln 0 (.ls 0)) 1 .ln)) := by native_decide

example : linearScanRegAlloc 2 [] (.delta [0, 2, 5] [4, 7]) [] =
    .success (.bs (.bs .ln 1 (.ls 2)) 0 (.bn (.ls 3) (.bn .ln (.ls 3)))) := by native_decide

example : linearScanRegAlloc 2 [(3, (5, 7))] (.seq (.delta [3, 5] [7, 1]) (.delta [7] [5])) [(5, 1)] =
    .success (.bn .ln (.bs (.ls 1) 0 (.bs .ln 3 (.ls 2)))) := by native_decide

end Flapjack.Test.LinearScanProductionTop
