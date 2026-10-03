import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.LabProps.SectionEnd
import Flapjack.Compiler.Backend.WordGcFunctions.HasFpOps
import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Assembly
import Flapjack.Compiler.Backend.StackRemove.Proofs.AsmName
import Flapjack.Compiler.Backend.StackRawCall.Proofs.AsmNames
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Conventions

/-! The encoding and initial-state group of `stack_to_labProofScript.sml:3620-3799`.
`flatten_line_ok_pre` and `compile_all_enc_ok_pre` live in
`StackToLab/Proofs/Encoding`; this module holds the remaining declarations of
the group. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit Flapjack.Compiler.Encoders.Asm

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

/-- HOL `stack_to_lab_compile_all_enc_ok`. HOL's free `c c1 c2 c3 sp prog`
are implicit; all twenty premises are kept in order. `names_ok`, `fixed_names`,
`conf_ok (:'a)`, `addr_offset_ok`/`byte_offset_ok c 0w` and `all_enc_ok_pre`
are the reviewed `namesOkSptHOL`, `fixedNames`, `confOk width`,
`asmAddrOffsetOkExact`/`asmByteOffsetOkExact c 0` and `allEncOkPreHOL`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_to_lab_compile_all_enc_ok" (words_as_type_indexed_bitvec)]
theorem stackToLabCompileAllEncOk {width : Nat} [NeZero width] {c : AsmConfigExact width}
    {prog : List (Nat × HolProg width)} {c1 : StackToLab.Config} {c2 : DataToWord.Config}
    {c3 sp : Nat} :
    (∀ np ∈ prog, StackProps.stackAsmName c np.2) ∧
      (∀ np ∈ prog, StackProps.stackAsmRemove c np.2) ∧
      StackNames.namesOkSptHOL c1.regNames c.regCount c.avoidRegs ∧
      StackProps.fixedNames c1.regNames c ∧
      asmAddrOffsetOkExact c 0 = true ∧ goodDimindex width ∧ asmByteOffsetOkExact c 0 = true ∧
      (∀ n, n ≤ StackRemove.maxStackAlloc →
        c.validImm (.inl .sub) (BitVec.ofNat width (n * (width / 8))) = true ∧
        c.validImm (.inl .add) (BitVec.ofNat width (n * (width / 8))) = true) ∧
      c.validImm (.inl .add) 1 = true ∧ c.validImm (.inl .sub) 1 = true ∧
      c.validImm (.inl .add) 4 = true ∧ c.validImm (.inl .add) 8 = true ∧
      (∀ s, asmAddrOffsetOkExact c (StackRemove.storeOffset s) = true) ∧
      StackProps.regName 10 c ∧ StackProps.regName (sp + 2) c ∧ StackProps.regName (sp + 1) c ∧
      StackProps.regName sp c ∧ DataToWord.confOk width c2 ∧ sp ≠ 0 →
      LabProps.allEncOkPreHOL c (StackToLab.compile c1 c2 c3 sp c.addrOffset prog) := by
  rintro ⟨hn, hr, hno, hfix, h0, hdim, hb0, himm, ha1, hs1, h4, h8, hst, h10, hk2, hk1, hk,
    hconf, hk0⟩
  have hraw := StackRawCall.stackAllocStackAsmConvs (c := c) (prog := prog)
  have halloc := StackAlloc.stack_alloc_stack_asm_convs (conf := c2)
    ⟨hraw.1 ▸ hn, hraw.2 ▸ hr, hconf, h0, h10, hdim, h8, h4, ha1, hs1⟩
  have hremove := StackRemove.Proofs.AsmName.stackRemoveStackAsmName (jump := c1.jump)
    (genGc := StackToLab.isGenGc c2.gcKind) (maxHeap := c3) (start := BvlToBvi.initGlobalsLocation)
    ⟨halloc.1, halloc.2, h0, hdim, himm, h4, h8, hst,
      StackRemove.Proofs.AsmName.regName_of_le h10 (by omega), hk2, hk1, hk, hk0⟩
  exact compileAllEncOkPreHOL c _ hb0 (StackNames.stackNamesStackAsmOk c c1.regNames _
    ⟨hremove, hno, hfix⟩)

end Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
