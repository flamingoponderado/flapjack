import Flapjack.Pancake.Proofs.PanToTarget.AssemblyInitCode
import Flapjack.Compiler.Backend.BackendProof.ReadLimits
import Flapjack.Pancake.Proofs.PanToTarget.WordToWordNoInstall
import Flapjack.Pancake.Proofs.PanToWord.NoInstallCode
import Flapjack.Pancake.Proofs.PanToWord

/-!
# `pan_to_target_compile_semantics` assembly, stage G (resource-limit implication)

The resource-limit implication of the single HOL proof of
`pan_to_target_compile_semantics` (`pan_to_targetProofScript.sml:2285-2506`):
`option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms)))` implies
`word_lang_safe_for_space wst InitGlobals_location` for the word initial state `wst`
built on the stack state of `full_make_init`.  Not a HOL theorem, so untagged.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Stage G of the HOL proof (lines 2285-2506).  `wprog`/`wconf` are the
`word_to_word`/`word_to_stack` results of `compile_prog_max` and `stack_max` its
depth bound; the lab state `t` satisfies the `full_make_init_semantics` hypotheses
with `full_make_init ... = (sst, SOME x)`, and its `len`/`ptr2`/`len2` registers hold
the machine's initial register words.  The pointer premises are the top theorem's
(`adj_ptr2 ≤ ptr2 ≤ adj_ptr4`, the heap-size bound and the alignment); `hnoerr` is
the no-`Error` fact HOL derives from `semantics wst InitGlobals_location ≠ Fail`. -/
theorem panToTargetResourceLimit {width : Nat} [NeZero width] {C F S Q : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ms : S)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × HolProg width)) (stackMax : Option Nat)
    {sp dataSp : Nat} {offset : BitVec width × BitVec width}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {saveRegs : Nat → Bool}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C F}
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hA : Assumptions c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
      sp offset bitmaps p t saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) sp offset bitmaps p t saveRegs dataSp
      coracle = (sst, some x))
    (h2 : t.regs t.lenReg = .word (mc.target.getReg ms t.lenReg))
    (h3 : t.regs t.ptr2Reg = .word (mc.target.getReg ms t.ptr2Reg))
    (h4 : t.regs t.len2Reg = .word (mc.target.getReg ms t.len2Reg))
    (hlo : mc.target.getReg ms t.lenReg +
        bytesInWord width * BitVec.ofNat width maxStackAlloc ≤ mc.target.getReg ms t.ptr2Reg)
    (hhi : mc.target.getReg ms t.ptr2Reg ≤
        mc.target.getReg ms t.len2Reg - bytesInWord width * BitVec.ofNat width maxStackAlloc)
    (hheap : (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg).toNat ≤
        (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
        2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
        (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg) = true)
    (hni : WordProps.noInstallCode (sptFromAList wprog))
    (hna : WordProps.noAllocCode (sptFromAList wprog))
    (hnoerr : ∀ k res t',
      evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
          { WordToStack.Native.Initialization.makeInit mc.target.config
              (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
              (sptFromAList wprog) worac with clock := k } = (res, t') →
        res ≠ some WordSemResult.error) :
    optionLt stackMax
        (some (BackendProof.readLimits mc.target.config c mc ms).1) = true →
      WordSemStateFiniteExact.wordLangSafeForSpace
        (WordToStack.Native.Initialization.makeInit mc.target.config
          (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
          (sptFromAList wprog) worac) BvlToBvi.initGlobalsLocation := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f4, f3, f2, -⟩ := id hA
  have hcomm : mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg =
      -1 * mc.target.getReg ms t.lenReg + mc.target.getReg ms t.ptr2Reg := BitVec.add_comm _ _
  have hle := panToTargetStackLimitLeInitStack _ _ _ hA hfmi h2 h3 h4
    (by rwa [BitVec.mul_comm] at hlo) (by rwa [BitVec.mul_comm] at hhi)
    (by rw [← hcomm, Nat.mul_comm]; exact hheap) hheapLt halign
  have hrl : (BackendProof.readLimits mc.target.config c mc ms).1 =
      (InitLimits.getStackHeapLimit (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.getReg ms t.lenReg, mc.target.getReg ms t.ptr2Reg,
          mc.target.getReg ms t.len2Reg)).1 := by
    simp only [BackendProof.readLimits, f2, f3, f4]
  rw [hrl]
  exact panToTargetSafeForSpaceOfLimit mc.target.config sst wprog worac _ _ stackMax
    (by rw [hmax, hwts]) hle hni hna hnoerr

/-- A word state whose `semantics` from `start` is not `Fail` never reaches `Error` on
the entry call, for any clock (HOL lines 1724-1727, from `wordSem$semantics_def`). -/
theorem wordNoErrorOfSemanticsNotFail {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (start : Nat)
    (hsem : WordSemStateFiniteExact.semantics s start ≠ .fail) :
    ∀ k res t',
      evaluate (.call none (some start) [0] none) { s with clock := k } = (res, t') →
        res ≠ some WordSemResult.error := by
  intro k res t' h hres
  apply hsem
  unfold WordSemStateFiniteExact.semantics
  rw [if_pos ⟨k, by simp only [h, hres]⟩]

/-- Stage G with its compiler and semantic premises discharged as in HOL (lines
1716-1736 and 2285-2312): `no_install`/`no_alloc` of the compiled word code come from
`word_to_word_compile_no_install_no_alloc` on the `pan_to_word` output, and the
no-`Error` fact from `semantics wst InitGlobals_location ≠ Fail`. -/
theorem panToTargetResourceLimitOfSemantics {width : Nat} [NeZero width] {C F S Q : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ms : S)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × HolProg width)) (stackMax : Option Nat)
    {sp dataSp : Nat} {offset : BitVec width × BitVec width}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {saveRegs : Nat → Bool}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C F}
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hA : Assumptions c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
      sp offset bitmaps p t saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) sp offset bitmaps p t saveRegs dataSp
      coracle = (sst, some x))
    (h2 : t.regs t.lenReg = .word (mc.target.getReg ms t.lenReg))
    (h3 : t.regs t.ptr2Reg = .word (mc.target.getReg ms t.ptr2Reg))
    (h4 : t.regs t.len2Reg = .word (mc.target.getReg ms t.len2Reg))
    (hlo : mc.target.getReg ms t.lenReg +
        bytesInWord width * BitVec.ofNat width maxStackAlloc ≤ mc.target.getReg ms t.ptr2Reg)
    (hhi : mc.target.getReg ms t.ptr2Reg ≤
        mc.target.getReg ms t.len2Reg - bytesInWord width * BitVec.ofNat width maxStackAlloc)
    (hheap : (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg).toNat ≤
        (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
        2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
        (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg) = true)
    (hsem : WordSemStateFiniteExact.semantics
        (WordToStack.Native.Initialization.makeInit mc.target.config
          (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
          (sptFromAList wprog) worac) BvlToBvi.initGlobalsLocation ≠ .fail) :
    optionLt stackMax
        (some (BackendProof.readLimits mc.target.config c mc ms).1) = true →
      WordSemStateFiniteExact.wordLangSafeForSpace
        (WordToStack.Native.Initialization.makeInit mc.target.config
          (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
          (sptFromAList wprog) worac) BvlToBvi.initGlobalsLocation := by
  obtain ⟨hni, hna⟩ := PanToTarget.word_to_word_compile_no_install_no_alloc c.wordToWordConf
    mc.target.config _ col wprog
    ⟨hwtw, panToWordFirstCompileProgAllDistinctHOL _ panCode hnodup,
      PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl,
      PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl⟩
  exact panToTargetResourceLimit c mc ms wprog bitmaps wconf fs p stackMax worac hwts hmax hA
    hfmi h2 h3 h4 hlo hhi hheap hheapLt halign hni
    (hna (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl))
    (wordNoErrorOfSemanticsNotFail _ _ hsem)

end Flapjack.Pancake.Proofs.PanToTarget
