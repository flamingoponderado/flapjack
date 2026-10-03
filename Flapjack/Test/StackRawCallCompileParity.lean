import Flapjack.Compiler.Backend.StackRawCall

/-! Complete outputs captured independently from original stack_rawcall compile.
These kernel fixtures do not establish executed routing or full simulation. -/
namespace Flapjack.Test.StackRawCallCompileParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall
private def tail : HolProg 64 := .seq (.stackFree 4) (.call none (.inl 7) none)
example : compile ([] : List (Nat × HolProg 64)) = [] := by cbv
example : compile [(3,.loop tail),(7,.seq (.stackAlloc 4) .skip)] =
    [(3,.loop (.rawCall 7)),(7,.seq (.stackAlloc 4) .skip)] := by cbv
example : compile [(3,.loop tail),(7,.seq (.stackAlloc 4) .skip),
    (7,.stackAlloc 9),(7,.seq (.stackAlloc 6) .skip)] =
    [(3,.loop (.seq .tick (.seq (.stackAlloc 2) (.rawCall 7)))),
      (7,.seq (.stackAlloc 4) .skip),(7,.stackAlloc 9),(7,.seq (.stackAlloc 6) .skip)] := by cbv
example : compile [(3,.loop tail),(7,.stackAlloc 4)] =
    [(3,.loop tail),(7,.stackAlloc 4)] := by cbv
example : compile ([(9,.seq (.stackAlloc 0) .skip),
    (3,.seq (.stackFree 0) (.call none (.inl 9) none))] : List (Nat × HolProg 64)) =
    [(9,.seq (.stackAlloc 0) .skip),(3,.seq (.stackFree 0) (.call none (.inl 9) none))] := by cbv
end Flapjack.Test.StackRawCallCompileParity
