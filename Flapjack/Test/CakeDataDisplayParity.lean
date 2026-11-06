import Flapjack.Compiler.Backend.PresLang.Data
import Flapjack.Compiler.Backend.BvlToBvi.Stubs
import Flapjack.Compiler.Backend.BviToData.Compile

/-! First `after bvi_to_data` function from the pinned CakeML explorer
regression program. The function is generated from the actual BVI stub. -/
namespace Flapjack.Test.CakeDataDisplayParity
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def expected : String :=
  "(func AllocGlobal@62 (0)\n   (seq\n      skip\n      (1 := GlobalsPtr () none)\n" ++
  "      skip\n      (2 := (Const 0) () none)\n      skip\n      (3 := El (1 2) none)\n" ++
  "      skip\n      skip\n      (4 := Add (0 3) (some {0,1,3}))\n" ++
  "      skip\n      (5 := Length (1) none)\n      skip\n      skip\n" ++
  "      (6 := (Const 0) () none)\n      skip\n      (7 := Update (1 6 4) none)\n" ++
  "      skip\n      skip\n      (8 := Less (4 5) (some {0,1,3,4,5,7}))\n" ++
  "      (if 8 (return (7))\n         (seq\n            skip\n            (10 := (Const 0) () none)\n" ++
  "            skip\n            skip\n            (11 := Add (4 4) (some {0,1,3,4,5,7,10}))\n" ++
  "            (12 := RefArray (11 10) (some {0,1,3,4,5,7,10,11}))\n" ++
  "            skip\n            (13 := SetGlobalsPtr (12) none)\n" ++
  "            skip\n            skip\n            skip\n            (14 := (Const 1) () none)\n" ++
  "            skip\n            (15 := Sub (5 14) (some {0,1,3,4,5,7,12,13,14}))\n" ++
  "            (call none CopyGlobals@63 (12 1 15) none)))))\n\n"

private def actual : Option String := do
  let (p, _, _) ← BviToData.compileFuel 2000 1 [0] true [] BvlToBvi.allocGlobalCode.2
  let names := sptInsert 62 (ofString "AllocGlobal") (sptInsert 63 (ofString "CopyGlobals") .ln)
  pure (String.join (PresLang.Data.functions names [(62, 1, p)]))

#guard actual == some expected

private def render (fuel : Nat) (p : DataLang.Prog) : String :=
  String.join (displayStrTreeToStrings "" (displayToStrTree (PresLang.Data.program fuel .ln p)))

#guard render 0 .skip == "..."
#guard render 1 (.seq .skip .tick) == "(seq)"
#guard render 2 (.seq .skip .tick) == "(seq\n   ...)"
#guard render 3 (.seq .skip .tick) == "(seq\n   skip\n   ...)"

end Flapjack.Test.CakeDataDisplayParity
