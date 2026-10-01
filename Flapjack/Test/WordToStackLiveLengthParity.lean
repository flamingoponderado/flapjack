import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveLength

namespace Flapjack.Test.WordToStackLiveLengthParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native

/-- Same-input regression applications to the actual native evaluator output.
This helper is test infrastructure, not a separate HOL port. -/
private theorem accounting {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (h : (appListAppend bs.1).length ≤ bs.2) :
    let bs2 := (wLiveNative live bs frame).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧
      bs.2 - (appListAppend bs.1).length = bs2.2 - (appListAppend bs2.1).length :=
  wLiveLength live bs frame _ _ ⟨rfl,h⟩

example : let bs := ((AppList.list [4] : AppList (BitVec 64)),1)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,0,7)).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧ bs.2 - (appListAppend bs.1).length =
      bs2.2 - (appListAppend bs2.1).length := accounting _ _ _ (by decide)
example : let bs := ((AppList.nil : AppList (BitVec 64)),0)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,1,1)).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧ bs.2 - (appListAppend bs.1).length =
      bs2.2 - (appListAppend bs2.1).length := accounting _ _ _ (by decide)
example : let bs := ((AppList.list [4] : AppList (BitVec 64)),9)
    let bs2 := (wLiveNative (.ln,.ln) bs (4,2,5)).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧ bs.2 - (appListAppend bs.1).length =
      bs2.2 - (appListAppend bs2.1).length := accounting _ _ _ (by decide)
example : let bs := ((AppList.append (.list [4]) (.append .nil (.list [7,8])) : AppList (BitVec 64)),3)
    let bs2 := (wLiveNative (.ln,.ls ()) bs (0,3,8)).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧ bs.2 - (appListAppend bs.1).length =
      bs2.2 - (appListAppend bs2.1).length := accounting _ _ _ (by decide)
example : let bs := ((AppList.nil : AppList (BitVec 64)),12)
    let bs2 := (wLiveNative (.bs .ln () .ln,.bn .ln .ln) bs (0,1,0)).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧ bs.2 - (appListAppend bs.1).length =
      bs2.2 - (appListAppend bs2.1).length := accounting _ _ _ (by decide)
example : let bs := ((AppList.list [4] : AppList (BitVec 8)),2)
    let bs2 := (wLiveNative (.ln,.ln) bs (2,1,9)).2
    (appListAppend bs2.1).length ≤ bs2.2 ∧ bs.2 - (appListAppend bs.1).length =
      bs2.2 - (appListAppend bs2.1).length := accounting _ _ _ (by decide)

end Flapjack.Test.WordToStackLiveLengthParity
