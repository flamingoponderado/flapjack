module

public import Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement

import all Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement
public meta import Flapjack.Compiler.Backend.BviLet.SourceSing
public meta import Flapjack.Compiler.Backend.BviLet.Compile

@[expose] public section

/-! Replays original HOL `compile_exp` observations from bvi_let_compile_probe. -/
open Flapjack.Compiler.Backend.BviLet

#guard compileSing [] 0 (.let [.var 3, .var 1] (.var 1)) ==
  .let [.var 3] (.var 2)

#guard compileSing [] 0 (.let [.var 3, .var 1] (.var 0)) ==
  .let [.op (.intOp (.const 0)) [], .op (.intOp (.const 0)) []] (.var 5)

#guard compileSing [] 0 (.let [] (.var 2)) == .var 2

#guard compileBounded 0 [] 0 (.let [.var 3, .var 1] (.var 1)) ==
  some (.let [.var 3] (.var 2))
