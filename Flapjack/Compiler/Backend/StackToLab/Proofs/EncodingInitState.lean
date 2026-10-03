import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.LabProps.SectionEnd
import Flapjack.Compiler.Backend.WordGcFunctions.HasFpOps

/-! The encoding and initial-state group of `stack_to_labProofScript.sml:3620-3799`.
`flatten_line_ok_pre` and `compile_all_enc_ok_pre` live in
`StackToLab/Proofs/Encoding`; this module holds the remaining declarations of
the group. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

/-- HOL `EVERY_sec_ends_with_label_MAP_prog_to_section`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "EVERY_sec_ends_with_label_MAP_prog_to_section" (words_as_type_indexed_bitvec)]
theorem everySecEndsWithLabelMapProgToSection {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width),
      ∀ sec ∈ prog.map progToSectionHOL, LabProps.secEndsWithLabelNative sec := by
  intro prog sec hsec
  obtain ⟨⟨n, p⟩, _, rfl⟩ := List.mem_map.mp hsec
  rw [progToSection_eq]
  simp [LabProps.secEndsWithLabelNative, LabSem.isLabelHOL]

/-- HOL `full_make_init_has_fp_ops`: the floating-point flags of the data
configuration do not affect `full_make_init`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem fullMakeInitHasFpOps {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dconf : DataToWord.Config} {b1 b2 : Bool} {mheap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {s : LabSem.State width C F} {saveRegs : Nat → Bool}
    {dsp : Nat} {cor : Nat → C × List (Nat × HolProg width) × List (BitVec width)} :
    fullMakeInit stackConf { dconf with hasFpOps := b1, hasFpTern := b2 } mheap sp offset bitmaps
        code s saveRegs dsp cor =
      fullMakeInit stackConf dconf mheap sp offset bitmaps code s saveRegs dsp cor := by
  unfold fullMakeInit StackAlloc.makeInit
  rw [WordGcFunctions.wordGcFun_hasFpOps]
  rfl

end Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
