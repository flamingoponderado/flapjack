import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabChain
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyResourceStage

/-!
# `pan_to_target_compile_semantics` assembly, lab chain with the resource limit

The lab-state chain of the HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:1440-2506`) with the resource-limit implication of
lines 2285-2506 applied: the lab semantics of the initial lab state lies in
`extend_with_resource_limit' (option_lt stack_max (SOME (FST (read_limits ...))))` of
the Pancake behaviour.  Intermediate step of the single HOL proof, so untagged.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

open Classical StackToLab.Proofs.FullMakeInitSemantics LabToTarget in
/-- Stage E over the top theorem's inputs (HOL lines 1737-1929): for the initial lab
state of `pan_installed`'s components and the `compile_prog_max` results,
`full_make_init` succeeds and `init_code` runs on its stack-names state without a
result, with `init_code_thm`'s facts on the lab `len`/`ptr2`/`len2` register words. -/
theorem panToTargetInitStage {width : Nat} [NeZero width] {S Q F C : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState F)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltc : C)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, c'', fs, p))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true))) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
    let labst := LabToTarget.makeInit (C := C) mc ffi t m
      (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    let saveRegs := fun k => decide (k ∈ mc.calleeSavedRegs)
    let sst := (StackToLab.Proofs.FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst saveRegs dataSp (fun _ => (ltc, [], []))).1
    (∃ x, StackToLab.Proofs.FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst saveRegs dataSp (fun _ => (ltc, [], [])) =
        (sst, some x)) ∧
    ∃ (t' : StackSemStateFiniteExact width C F) (w2 w3 w4 : BitVec width),
      StackSemEvaluate.evaluate
          (StackRemove.initCode (StackToLab.isGenGc c.dataConf.gcKind) maxHeap sp,
            s2 c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p labst saveRegs
              (fun _ => (ltc, [], []))) = (none, t') ∧
      labst.regs labst.lenReg = .word w2 ∧ labst.regs labst.ptr2Reg = .word w3 ∧
      labst.regs labst.len2Reg = .word w4 ∧
      holByteAligned w2 = true ∧ holByteAligned w4 = true ∧ w2 < w4 := by
  intro regNames r1 r2 heapStackDm sp maxHeap labst saveRegs sst
  have hA := panToTargetFullMakeInitAssumptions (C := C) c mc ffi t m bitmapPtr bitmapsDm sdm ms
    comp bytes cbspace ltc panCode col wprog bitmaps c'' fs p dataSp hcfg hmc hinit hisa hwtw hwts
    hnodup hpi
  refine ⟨?_, ?_⟩
  · rcases hfm : StackToLab.Proofs.FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst saveRegs dataSp (fun _ => (ltc, [], []))
      with ⟨s', opt⟩
    obtain ⟨hopt, -⟩ := fullMakeInitSemantics (s := s') (opt := opt) ⟨hfm, hA⟩
    obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hopt
    exact ⟨x, by simp only [sst, hfm]⟩
  · obtain ⟨t', w2, w3, w4, hev, g2, g3, g4, a2, a4, lt, -⟩ := panToTargetInitCodeRun hA
    exact ⟨t', w2, w3, w4, hev, g2, g3, g4, a2, a4, lt⟩

open Classical StackToLab.Proofs.FullMakeInitSemantics LabToTarget in
/-- Lab chain with stage G (HOL lines 1440-2506): under the hypotheses of
`panToTargetLabSemantics` and `stack_max` of `compile_prog_max`, the lab semantics
of the initial lab state is in `extend_with_resource_limit'` of the Pancake
declaration semantics with the original resource flag
`option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms)))`. -/
theorem panToTargetLabSemanticsResource {width : Nat} [NeZero width] {S Q C σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltc : C)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (s : PanSemStateFiniteExact width σ) (start : MlS)
    (globalsSize heapLen : Nat) (stackMax : Option Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, c'', fs, p))
    (hmax : stackMax = WordDepth.maxDepth c''.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    -- `pan_installed`'s components
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)))
    -- the top theorem's register, bound and memory hypotheses
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (StackRemove.bytesInWord width).toNat *
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hbe : mc.target.config.bigEndian = s.be) (hffi : s.ffi = ffi)
    (hheapLen : heapLen = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs =
      StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heapLen - globalsSize))
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
    let labst := LabToTarget.makeInit (C := C) mc ffi t m
      (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL
      (optionLt stackMax (some (BackendProof.readLimits mc.target.config c mc ms).1))
      (fun b => b = PanSemStateFiniteExact.semanticsDecls s start panCode)
      (LabSem.semantics labst) := by
  intro regNames r1 r2 heapStackDm sp maxHeap labst
  obtain ⟨hmem, hsemEq, x, hfmi⟩ := panToTargetLabSemantics c mc ffi t m bitmapPtr bitmapsDm sdm
    ms comp bytes cbspace ltc panCode col wprog bitmaps c'' fs p dataSp s start globalsSize heapLen
    hcfg hmc hinit hisa hwtw hwts hnodup hpm hgi hsdm hpi hbase hlt hlo hhi hheap hheapLt halign
    hbe hffi hheapLen hglobLe hmemaddrs htop hstart hsize hparams halloc hcode hglobals hlocals
    heids heshapes hfail
  have hA := panToTargetFullMakeInitAssumptions (C := C) c mc ffi t m bitmapPtr bitmapsDm sdm ms
    comp bytes cbspace ltc panCode col wprog bitmaps c'' fs p dataSp hcfg hmc hinit hisa hwtw hwts
    hnodup hpi
  refine extendPrime_flag_mono _ _ (fun hres => decide_eq_true
    (panToTargetResourceLimitOfSemantics c mc ms panCode col wprog bitmaps c'' fs p stackMax _
      hwtw hnodup hwts hmax hA hfmi
      (panToTargetLabRegWord mc ffi t _ _ _ ms _ comp _ cbspace _ hgi.1 _ hmc.2.2.2.1)
      (panToTargetLabRegWord mc ffi t _ _ _ ms _ comp _ cbspace _ hgi.1 _ hmc.2.2.2.2.1)
      (panToTargetLabRegWord mc ffi t _ _ _ ms _ comp _ cbspace _ hgi.1 _ hmc.2.2.2.2.2.1)
      hlo hhi hheap hheapLt halign (hsemEq ▸ hfail) hres)) _ _ hmem

end Flapjack.Pancake.Proofs.PanToTarget
