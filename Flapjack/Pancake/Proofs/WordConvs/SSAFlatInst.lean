import Flapjack.Pancake.Proofs.WordConvs.SSAFlatHelpers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Original complete Inst case of SSA flat-expression preservation, including
all native instruction constructors, FP width branches and fallback clauses. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "ssa_cc_trans_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_flatExpInst {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_source : flatExpConventions (.inst instruction) = true) :
    flatExpConventions (ssaCcTrans (.inst instruction) ssa next tables).1 = true := by
  simp only [ssaCcTrans]
  fun_cases ssaCcTransInst instruction ssa next <;> simp [flatExpConventions]

end Flapjack.WordAlloc
