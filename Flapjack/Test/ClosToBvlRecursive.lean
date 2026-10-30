import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Total

/-! Replays the recursive-closure layout observations captured from the
pinned HOL compiler; these finite examples do not establish equivalence. -/
namespace Flapjack.Test.ClosToBvlRecursive

open Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.Bvl

example : reccLetsHOL 4 [1, 2] 2 (.var 0) =
    .let [reccLet 6 1 1] (.let [reccLet 4 2 0] (.var 0)) := by rfl

example : reccLets? 4 [1, 2] 2 (.var 0) =
    some (.let [reccLet 6 1 1] (.let [reccLet 4 2 0] (.var 0))) := by rfl

example : buildReccLetsHOL [1, 2] [5] 4 2 (.var 0) =
    .let [.let [.op (.memOp .ref) [.var 5, mkConst 0, mkConst 0]] (reccLet0 6 2 1)]
      (.let [reccLet 4 1 0] (.var 0)) := by rfl

example : buildReccLets? [1, 2] [5] 4 2 (.var 0) =
    some (.let [.let [.op (.memOp .ref) [.var 5, mkConst 0, mkConst 0]] (reccLet0 6 2 1)]
      (.let [reccLet 4 1 0] (.var 0))) := by rfl

end Flapjack.Test.ClosToBvlRecursive
