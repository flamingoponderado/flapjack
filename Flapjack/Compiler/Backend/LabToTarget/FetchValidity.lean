import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem

/-- Original full validity implication over the native fetched instruction and its physical byte position.
The original configuration, label map, FFI list, indices, code and fetched line remain quantified. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_enc_ok_asm_fetch_aux_IMP_line_ok" (words_as_type_indexed_bitvec)]
theorem allEncOk_fetch_lineOk {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pc n : Nat)
    (code2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (line : LabLineHOL width) :
    allEncOk c labs ffis n code2 ∧ asmFetchAux pc code2 = some line →
    lineOk c labs ffis (posVal pc n code2) line := by
  fun_induction posVal pc n code2 generalizing line <;>
    simp_all [allEncOk, asmFetchAux]
  intro h _ heq
  exact heq ▸ h

end Flapjack.Compiler.Backend.LabToTarget
