import Flapjack.Pancake.WordLang.CutsetsMax

namespace Flapjack.Test.WordLangCutsetsMaxParity
open Flapjack

-- Kernel replays of freshly captured original cutsets_max rows.
example : cutsetsMaxHOL (.ln, .ln) = 0 := by simp [cutsetsMaxHOL, sptToAList, sptFoldi, maxList]
example : cutsetsMaxHOL (sptInsert 5 () .ln, .ln) = 5 := by simp [cutsetsMaxHOL, sptInsert, sptToAList, sptFoldi, lrNext, maxList]
example : cutsetsMaxHOL (.ln, sptInsert 17 () .ln) = 17 := by simp [cutsetsMaxHOL, sptInsert, sptToAList, sptFoldi, lrNext, maxList]
example : cutsetsMaxHOL (sptInsert 5 () .ln, sptInsert 17 () .ln) = 17 := by simp [cutsetsMaxHOL, sptInsert, sptToAList, sptFoldi, lrNext, maxList]
example : cutsetsMaxHOL (.ls (), .ln) = 0 := by simp [cutsetsMaxHOL, sptToAList, sptFoldi, maxList]
example : cutsetsMaxHOL (.bn .ln .ln, .ln) = 0 := by simp [cutsetsMaxHOL, sptToAList, sptFoldi, maxList]
example : cutsetsMaxHOL (.bs .ln () (.ls ()), .ln) = 1 := by simp [cutsetsMaxHOL, sptToAList, sptFoldi, lrNext, maxList]
example : cutsetsMaxHOL (sptInsert 87 () (sptInsert 5 () .ln), sptInsert 17 () .ln) = 87 := by simp [cutsetsMaxHOL, sptInsert, sptToAList, sptFoldi, lrNext, maxList]

end Flapjack.Test.WordLangCutsetsMaxParity
