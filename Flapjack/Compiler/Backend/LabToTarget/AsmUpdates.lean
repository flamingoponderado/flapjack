import Flapjack.Compiler.Encoders.AsmSem.Arithmetic
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders.AsmSem
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "upd_pc_with_pc" (words_as_type_indexed_bitvec)]
theorem updPc_with_pc {width : Nat} [NeZero width] (s : AsmState width) : updPc s.pc s = s := rfl
end Flapjack.Compiler.Backend.LabToTarget
