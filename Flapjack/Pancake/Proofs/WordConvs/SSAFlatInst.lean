module

public import Flapjack.Pancake.Proofs.WordConvs.SSAFlatHelpers
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
public import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard

@[expose] public section

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Original Inst constructor case of SSA flat-expression preservation, including
all native instruction constructors, FP width branches and fallback clauses.

This is the `prog = Inst instruction` instance of HOL
`ssa_cc_trans_flat_exp_conventions` (`wordConvsProofScript.sml:1417-1430`), which
quantifies an arbitrary program. A specialized instance is not an exact port of that
statement, so the `@[hol]` tag was withdrawn (task 171); this remains untagged
infrastructure. The exact general port is the tagged `ssaCcTrans_flatExpConventions`
in `SSAFlatProgram.lean`. -/
theorem ssaCcTrans_flatExpInst {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_source : flatExpConventions (.inst instruction) = true) :
    flatExpConventions (ssaCcTrans (.inst instruction) ssa next tables).1 = true := by
  simp only [ssaCcTrans]
  fun_cases ssaCcTransInst instruction ssa next <;> simp [flatExpConventions]

end Flapjack.WordAlloc
