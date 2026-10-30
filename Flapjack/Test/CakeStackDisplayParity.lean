import Flapjack.Compiler.Backend.PresLang.Stack
import Flapjack.Compiler.Backend.WordToStack.NativeStubs

/-! The first two functions in pinned CakeML's `after word_to_stack` stage.
The inputs are the actual width-indexed stack stubs. -/
namespace Flapjack.Test.CakeStackDisplayParity
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def expected : String :=
  "(func _Raise@5\n   (seq\n      (22 <- Handler)\n      (stack_set_size 22)\n" ++
  "      skip\n      (22 := stack[0x2])\n      (Handler <- 22)\n" ++
  "      (22 := stack[0x1])\n      (stack_free 3)\n      (raise 22)))\n\n" ++
  "(func _StoreConsts@6\n   (seq\n      (store_consts 22 23)\n      (return 0)))\n\n"

private def actual : String :=
  let names := sptInsert 5 (ofString "_Raise") (sptInsert 6 (ofString "_StoreConsts") .ln)
  let first := PresLang.Stack.fromHol (WordToStack.Native.raiseStubNative (width := 64) false 22)
  let second := PresLang.Stack.fromHol (WordToStack.Native.storeConstsStubNative (width := 64) 22)
  String.join (PresLang.Stack.functions names [(5, first), (6, second)])

#guard actual == expected

private def render (fuel : Nat) (p : StackLang.ProgM (BitVec 64)) : String :=
  String.join (displayStrTreeToStrings "" (displayToStrTree (PresLang.Stack.program fuel .ln p)))

#guard render 0 .skip == "..."
#guard render 2 (.seq .skip .tick) == "(seq\n   ...)"
#guard render 3 (.seq .skip .tick) == "(seq\n   skip\n   ...)"
#guard render 2 (.call (some (.skip, 1, 2, 3)) (.inl 4) (some (.tick, 5, 6))) ==
  "(call (returning 1 2 3 skip) (direct 4) (handler 5 6 tick))"

end Flapjack.Test.CakeStackDisplayParity
