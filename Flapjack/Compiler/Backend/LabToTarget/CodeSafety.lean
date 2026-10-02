import Flapjack.Compiler.Backend.LabProps.CodeSafety
import Flapjack.FfiHOL

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Literal code/FFI-name safety disjunction. The FFI-name carrier retains exact MlString payloads and both alternatives. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_install_or_no_share_mem_def"
  (words_as_type_indexed_bitvec)]
def noInstallOrNoShareMem {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (ffiNames : List HolFfiName) : Prop :=
  (noShareMemInst code ∧ ∀ x ∈ ffiNames, ∃ name : MlString, x = .extCall name) ∨
    noInstall code

end Flapjack.Compiler.Backend.LabToTarget
