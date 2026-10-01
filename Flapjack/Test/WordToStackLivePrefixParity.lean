import Flapjack.Compiler.Backend.WordToStack.Proofs.LivePrefix

namespace Flapjack.Test.WordToStackLivePrefixParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native

/-- Same-input regression applications to the actual native evaluator output.
This helper is test infrastructure, not a separate HOL port. -/
private theorem actualPrefix {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) :
    (appListAppend bs.1).IsPrefix (appListAppend (wLiveNative live bs frame).2.1) :=
  wLiveIsPrefix live bs frame _ _ rfl

example : let bs := ((AppList.list [4] : AppList (BitVec 64)),1)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,0,7)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _
example : let bs := ((AppList.nil : AppList (BitVec 64)),0)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,1,1)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _
example : let bs := ((AppList.list [4] : AppList (BitVec 64)),9)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,2,5)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _
example : let bs := ((AppList.append (.list [4]) (.append .nil (.list [7,8])) : AppList (BitVec 64)),3)
    let bs2 := (wLiveNative (.ln,.ls ()) bs (0,3,8)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _
example : let bs := ((AppList.nil : AppList (BitVec 64)),12)
    let bs2 := (wLiveNative (.bs .ln () .ln,.bn .ln .ln) bs (0,1,0)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _
example : let bs := ((AppList.list [4] : AppList (BitVec 8)),2)
    let bs2 := (wLiveNative (.ln,.ln) bs (2,1,9)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _

example : let bs := ((AppList.list [4] : AppList (BitVec 64)),0)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,2,7)).2
    (appListAppend bs.1).IsPrefix (appListAppend bs2.1) := actualPrefix _ _ _

end Flapjack.Test.WordToStackLivePrefixParity
