import Flapjack.Compiler.Backend.LabToTarget.Labels

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Original annotated length: deliberately independent of encoded byte length. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_def"
  (words_as_type_indexed_bitvec)]
def lineLen {width : Nat} [NeZero width] :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Nat
  | .label _ _ len => len
  | .asm _ _ len => len
  | .labAsm _ _ _ len => len

end Flapjack.Compiler.Backend.LabToTarget
