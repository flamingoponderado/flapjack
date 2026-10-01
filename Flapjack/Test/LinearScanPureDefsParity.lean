import Flapjack.Compiler.Backend.LinearScan
namespace Flapjack.Test.LinearScanPureDefsParity
open RegAlloc LinearScan
-- Full-value replay of the fifteen original linear_scan_pure_defs_probe rows
-- (HOL `I`/`K 0` are `id`/`fun _ => 0`). These finite observations do not
-- prove allocator soundness or route these definitions into the compiler.
example : getLiveTree (.branch (some (sptInsert 3 () .ln)) (.delta [1] [2])
    (.set (sptInsert 5 () (sptInsert 4 () .ln)))) =
    .seq (.reads [3]) (.branch (.seq (.reads [2]) (.writes [1])) (.reads [5, 4])) := by
  decide +kernel
example : getLiveBackward (.seq (.writes [1]) (.branch (.reads [2, 1]) (.reads [3]))) .ln =
    .bn (.ls ()) (.bn .ln (.ls ())) := by decide +kernel
example : fixDomination (.reads [1]) = .seq (.writes [1]) (.reads [1]) := by decide +kernel
example : fixDomination (.writes [1]) = .writes [1] := by decide +kernel
example : checkLiveTree id (.seq (.writes [2]) (.reads [1, 2])) .ln .ln =
    some (.bn .ln (.ls ()), .bn .ln (.ls ())) := by decide +kernel
example : checkLiveTree (fun _ => 0) (.seq (.writes [2]) (.reads [1, 2])) .ln .ln = none := by
  decide +kernel
example : checkLiveTree id (.branch (.reads [1]) (.reads [2])) .ln .ln =
    some (.bn (.ls ()) (.ls ()), .bn (.ls ()) (.ls ())) := by decide +kernel
example : numsetListAddIfLt [1, 2, 1] 5 (sptInsert 1 7 .ln) = .bn (.ls 5) (.ls 5) := by
  decide +kernel
example : numsetListAddIfGt [1, 2, 1] 5 (sptInsert 1 7 .ln) = .bn (.ls 5) (.ls 7) := by
  decide +kernel
example : getIntervals (.seq (.writes [1]) (.reads [1, 2])) 0 .ln .ln =
    (-2, .bn .ln (.ls (-1)), .bn (.ls 0) (.ls 0)) := by decide +kernel
example : getIntervalsWithlive (.branch (.reads [1]) (.writes [2])) 0 .ln .ln
    (sptInsert 2 () .ln) = (-2, .ln, .bn (.ls 0) (.ls (-1))) := by decide +kernel
example : getIntervalsCt (.seq (.delta [1] [2])
    (.branch (some (sptInsert 3 () .ln)) (.delta [] [1]) (.set (sptInsert 2 () .ln)))) =
    (-7, .bn (.ls (-6)) (.bs .ln (-4) (.ls (-6))), .bn (.ls 0) (.bs .ln (-2) (.ls (-3)))) := by
  decide +kernel
example : sizeOfLiveTree (.seq (.writes [1]) (.branch (.reads [2, 1]) (.reads [3]))) = 3 := by
  decide +kernel
example : numsetListInsertNottailrec [4, 1, 2] .ln = .bn (.bs .ln () (.ls ())) (.ls ()) := by
  decide +kernel
example : numsetListInsert [4, 1, 2] .ln = .bn (.bs .ln () (.ls ())) (.ls ()) := by
  decide +kernel
end Flapjack.Test.LinearScanPureDefsParity
