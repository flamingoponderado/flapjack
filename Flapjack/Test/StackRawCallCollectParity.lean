import Flapjack.Compiler.Backend.StackRawCall
namespace Flapjack.Test.StackRawCallCollectParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall
example : seqStackAlloc (.stackAlloc 4 : HolProg 64) = none := rfl
example : seqStackAlloc (.seq (.stackAlloc 0) .skip : HolProg 64) = some 0 := rfl
example : seqStackAlloc (.seq .skip (.seq (.stackAlloc 4) .skip) : HolProg 64) = none := rfl
private def programs : List (Nat × HolProg 64) :=
  [(7,.seq (.stackAlloc 4) .skip), (7,.stackAlloc 9),
   (7,.seq (.stackAlloc 6) .skip), (9,.seq (.stackAlloc 0) .skip)]
example : [3,7,9,11].map (fun n => sptLookup n (collectInfo programs (sptInsert 3 8 .ln))) =
    [some 8, some 6, some 0, none] := by
  decide +kernel
end Flapjack.Test.StackRawCallCollectParity
