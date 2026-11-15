module

public import Flapjack.Pancake.Proofs.WordConvs.SSAFlatHelpers
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
public import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard

@[expose] public section

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-! The former untagged `ssaCcTrans_flatExpInst` helper was the `prog = Inst`
instance of HOL `ssa_cc_trans_flat_exp_conventions`. It had no user outside the
proof of the tagged `ssaCcTrans_flatExpConventions`, so it was retired and its
Inst case inlined there. -/

end Flapjack.WordAlloc
