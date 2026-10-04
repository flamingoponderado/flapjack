import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import Flapjack.Compiler.Backend.Proofs.WordConventions
import Flapjack.Pancake.Proofs.PanToWord.LabPres
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileBitmaps
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics
import Flapjack.SemanticsProps.Implements
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyStackToLab
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory

/-!
# `pan_to_target_compile_semantics` assembly, word-to-stack stage facts

Facts that the HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:1606-1622`) establishes before applying
`word_to_stackProof$compile_semantics`. Intermediate steps of the single HOL proof,
so untagged; premises are hypotheses of the top theorem or reviewed pass results.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang

/-- `ALOOKUP` misses a key absent from the list's keys (Flapjack infrastructure). -/
theorem panPropsALookupEq_eq_none {κ α : Type} [DecidableEq κ] (key : κ) :
    ∀ (l : List (κ × α)), (∀ e ∈ l, e.1 ≠ key) → panPropsALookupEq key l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro h
    obtain ⟨k, v⟩ := e
    simp only [panPropsALookupEq]
    have hk : k ≠ key := h (k, v) (by simp)
    simp only [hk, decide_false, Bool.false_eq_true, if_false]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- The word program has no entries at the two stub locations (HOL proof lines
1606-1622: `pan_to_word_compile_prog_lab_min` and the key equation of
`compile_to_word_conventions2`). -/
theorem panToTargetStubLocationsFree {width : Nat} [NeZero width]
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hisa : ac.isa ≠ .ag32)
    (hwtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wprog)) :
    panPropsALookupEq raiseStubLocation wprog = none ∧
      panPropsALookupEq storeConstsStubLocation wprog = none := by
  have hconv := BackendProof.compileToWordConventions2 wc ac _ col wprog hwtw
    (fun _ _ => Or.inr hisa)
  have hkeys := hconv.1
  have hmin := PanToWord.pan_to_word_compile_prog_lab_min ac.isa panCode _ rfl
  have hge : ∀ e ∈ wprog, 60 ≤ e.1 := by
    intro e he
    have : e.1 ∈ wprog.map Prod.fst := List.mem_map_of_mem he
    rw [hkeys] at this
    obtain ⟨e', he', heq⟩ := List.mem_map.mp this
    rw [← heq]; exact hmin e' he'
  constructor
  · exact panPropsALookupEq_eq_none _ _ (fun e he h => by
      have := hge e he; rw [h] at this
      simp [raiseStubLocation, wordNumStubs, stackNumStubs] at this)
  · exact panPropsALookupEq_eq_none _ _ (fun e he h => by
      have := hge e he; rw [h] at this
      simp [storeConstsStubLocation, wordNumStubs, stackNumStubs] at this)

/-- A successful `full_make_init` keeps the supplied bitmaps and installs the stack
program as the code (HOL proof lines 1563-1585: `make_init_opt`, `make_init_any`,
`init_reduce`). -/
theorem fullMakeInit_bitmaps_code {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × StackLang.HolProg width)) (s4 : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width))
    (s x : StackSemStateFiniteExact width C F)
    (h : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code s4
      saveRegs dataSp coracle = (s, some x)) :
    s.bitmaps = bitmaps ∧ s.code = sptFromAList code := by
  unfold StackToLab.Proofs.FullMakeInit.fullMakeInit at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, hopt⟩ := h
  constructor
  · simp only [StackAlloc.makeInit, StackRemove.Proofs.InitMake.makeInitAny, hopt]
    unfold StackRemove.Proofs.InitMake.makeInitOpt at hopt
    split at hopt
    · cases hopt
    · split at hopt
      · cases hopt; rfl
      · cases hopt
  · rfl

/-- `init_state_ok` for the stack state of `full_make_init` with the proof's empty
word oracle (HOL proof lines 1624-1647, via `IMP_init_state_ok`). -/
theorem panToTargetInitStateOk {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (c'' : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg width)) (cfg : C)
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap stk : Nat)
    (stoff : BitVec width × BitVec width) (labSt : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (sst xxx : StackSemStateFiniteExact width C F)
    (good : goodDimindex width) (hregs : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (hwts : WordToStack.Native.compileNative ac false wprog = (bitmaps, c'', fs, p))
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit scc dc maxHeap stk stoff bitmaps p labSt
      saveRegs dataSp (fun _ => (cfg, [], [])) = (sst, some xxx)) :
    WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount - (ac.avoidRegs.length + 5)) sst
      (fun _ => ((bitmaps.length, cfg), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))) := by
  have hbm := (WordToStack.Native.compileWordToStackBitmaps ac wprog bitmaps c'' (fs, p) hwts).1
  obtain ⟨t, rfl⟩ : ∃ t, bitmaps = 4 :: t := by
    cases bitmaps with
    | nil => exact absurd hbm id
    | cons h t => exact ⟨t, by simp_all⟩
  apply StackToLab.Proofs.EncodingInitState.impInitStateOk (labSt := labSt) (saveRegs := saveRegs)
    (dataSp := dataSp) (xxx := xxx) (scc := scc) (dc := dc) (maxHeap := maxHeap) (stk := stk)
    (stoff := stoff) (p6 := p)
  refine ⟨by omega, rfl, good, fun n => ?_, ?_, hfmi⟩
  · simp
  · funext n
    simp [WordToStack.Native.compileWordToStackNative, appListAppend, appendAux]

/-- The word-level initial state `wst = word_to_stack$make_init ... sst` built on the
stack state of a successful `full_make_init` satisfies the state premises of
`word_to_word_compile_semantics` (HOL proof lines 1686-1716: `gc_fun_const_ok` via
`gc_fun_const_ok_word_gc_fun`, empty stack, its code, and `lookup 0 locals`). -/
theorem panToTargetWordStateFacts {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap stk : Nat)
    (stoff : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (p : List (Nat × StackLang.HolProg width)) (labSt : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (soracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width))
    (sst xxx : StackSemStateFiniteExact width C F)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit scc dc maxHeap stk stoff bitmaps p labSt
      saveRegs dataSp soracle = (sst, some xxx)) :
    let wst := WordToStack.Native.Initialization.makeInit ac k sst code worac
    WordSimp.gcFunConstOk wst.gcFun ∧ wst.stack = [] ∧ wst.code = code ∧
      sptLookup 0 wst.locals = some (.loc 1 0) := by
  unfold StackToLab.Proofs.FullMakeInit.fullMakeInit at hfmi
  simp only [Prod.mk.injEq] at hfmi
  obtain ⟨rfl, -⟩ := hfmi
  refine ⟨?_, rfl, rfl, ?_⟩
  · exact DataToWord.Proofs.Gc.gcFunConstOkWordGcFun
  · simp [WordToStack.Native.Initialization.makeInit]; rfl

/-- A behaviour in `extend_with_resource_limit' b {w}` is `Fail` only when `w` is
(Flapjack infrastructure for the HOL proof's "elim stackSem ≠ Fail" steps,
lines 1653-1667). -/
theorem extendPrime_singleton_ne_fail (precise : Bool) (w r : HolBehaviour)
    (h : SemanticsPropsHOL.extendWithResourceLimitPrimeHOL precise (fun b => b = w) r)
    (hw : w ≠ .fail) : r ≠ .fail := by
  unfold SemanticsPropsHOL.extendWithResourceLimitPrimeHOL at h
  split at h
  · rw [h]; exact hw
  · rcases h with h | ⟨_, _, _, rfl, _, _⟩ | ⟨_, _, rfl, _, _⟩
    · rw [h]; exact hw
    · exact HolBehaviour.noConfusion
    · exact HolBehaviour.noConfusion

open Classical in
/-- The word-to-stack and word-to-word links of the HOL proof (lines 1649-1736): when
the source word semantics (code `wprog0`) is not `Fail`, the stack semantics of the
initial stack state lies in `extend_with_resource_limit'` of that word behaviour,
with the safe-for-space flag of the compiled word state. The premises are those of
`word_to_stackProof$compile_semantics` and `word_to_word_compile_semantics`. -/
theorem panToTargetWordChain {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wconf : WordToWord.Config)
    (wprog0 wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat))) (sst : StackSemStateFiniteExact width C F)
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start : Nat)
    (hwtw : WordToWord.compile wconf ac wprog0 = (col, wprog))
    (hgc : WordSimp.gcFunConstOk sst.gcFun)
    (hni0 : WordProps.noInstallCode (sptFromAList wprog0))
    (hna0 : WordProps.noAllocCode (sptFromAList wprog0))
    (hnm0 : WordProps.noMtCode (sptFromAList wprog0))
    (hnodup0 : (wprog0.map Prod.fst).Nodup)
    (hcode : sst.code = sptFromAList (WordToStack.Native.compileNative ac false wprog).2.2.2)
    (hinit : WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount - (5 + ac.avoidRegs.length)) sst worac)
    (hraise : panPropsALookupEq raiseStubLocation wprog = none)
    (hstore : panPropsALookupEq storeConstsStubLocation wprog = none)
    (hbm : (WordToStack.Native.compileNative ac false wprog).1 <+: sst.bitmaps)
    (hconv : ∀ entry ∈ wprog, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (ac.regCount - (5 + ac.avoidRegs.length)) entry.2.2 = true) :
    let wst := WordToStack.Native.Initialization.makeInit ac
      (ac.regCount - (5 + ac.avoidRegs.length)) sst (sptFromAList wprog) worac
    let wst0 := { wst with code := sptFromAList wprog0 }
    WordSemStateFiniteExact.semantics wst0 start ≠ .fail →
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL
      (decide (WordSemStateFiniteExact.wordLangSafeForSpace wst start))
      (fun b => b = WordSemStateFiniteExact.semantics wst0 start)
      (StackSemEvaluate.semantics start sst) := by
  intro wst wst0 hnf
  have heq : WordSemStateFiniteExact.semantics wst0 start =
      WordSemStateFiniteExact.semantics wst start :=
    WordToWord.word_to_word_compile_semantics wconf ac wprog0 col wprog wst0 start wst
      ⟨hwtw, hgc, hni0, hna0, hni0, hna0, hnm0, hnodup0, rfl, rfl, by
        simp [wst, WordToStack.Native.Initialization.makeInit]; rfl, rfl, rfl, hnf⟩
  rw [heq]
  exact WordToStackProofs.CompileSemantics.compileSemantics ac wprog sst _ worac start
    ⟨hcode, rfl, hinit, hraise, hstore, hbm, hconv, heq ▸ hnf⟩

/-- The stack-to-lab link of the HOL proof (lines 1552-1560): under the premises of
`stack_to_labProof$full_make_init_semantics`, a stack behaviour that is not `Fail`
is the lab behaviour of the initial lab state, so the lab semantics inherits any
`extend_with_resource_limit'` membership whose source behaviour is not `Fail`. -/
theorem panToTargetLabStackLink {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F} {opt : Option (StackSemStateFiniteExact width C F)}
    (precise : Bool) (w : HolBehaviour) (hw : w ≠ .fail)
    (hpre : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
        bitmaps code t saveRegs dataSp coracle = (s, opt) ∧
      goodDimindex width ∧
      t.code = StackToLab.compile stackConf dataConf maxHeap sp offset code ∧
      t.compileOracle = (fun n => ((coracle n).1,
        StackToLab.compileNoStubs stackConf.regNames stackConf.jump offset sp (coracle n).2.1)) ∧
      ¬t.failed = true ∧
      StackToLab.Proofs.MakeInit.memoryAssumption stackConf.regNames bitmaps dataSp t ∧
      StackRemove.maxStackAlloc ≤ maxHeap ∧
      ¬saveRegs t.linkReg = true ∧ t.pc = 0 ∧
      (∀ k i n, saveRegs k = true → t.ioRegs n i k = none) ∧
      (∀ k n, saveRegs k = true → t.ccRegs n k = none) ∧
      (∀ x : BitVec width, t.memDomain x = true → x.toNat % (width / 8) = 0) ∧
      (∀ x : BitVec width, t.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
      StackToLab.Proofs.GoodCode.goodCode sp code ∧
      (∀ n, StackToLab.Proofs.GoodCode.goodCode sp (coracle n).2.1) ∧
      10 ≤ sp ∧
      (∀ r ∈ [2, 3, 4], saveRegs (StackNames.findNameSpt stackConf.regNames (r + sp - 2)) = true) ∧
      StackNames.findNameSpt stackConf.regNames 4 = t.len2Reg ∧
      StackNames.findNameSpt stackConf.regNames 3 = t.ptr2Reg ∧
      StackNames.findNameSpt stackConf.regNames 2 = t.lenReg ∧
      StackNames.findNameSpt stackConf.regNames 1 = t.ptrReg ∧
      StackNames.findNameSpt stackConf.regNames 0 = t.linkReg ∧
      Function.Bijective (StackNames.findNameSpt stackConf.regNames))
    (hstack : SemanticsPropsHOL.extendWithResourceLimitPrimeHOL precise (fun b => b = w)
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s)) :
    opt ≠ none ∧
      SemanticsPropsHOL.extendWithResourceLimitPrimeHOL precise (fun b => b = w)
        (LabSem.semantics t) := by
  obtain ⟨hopt, hsem⟩ := StackToLab.Proofs.FullMakeInitSemantics.fullMakeInitSemantics hpre
  refine ⟨hopt, ?_⟩
  rw [hsem (extendPrime_singleton_ne_fail precise w _ hstack hw)]
  exact hstack

open StackToLab.Proofs.FullMakeInitSemantics LabToTarget in
/-- The hypotheses of `stack_to_labProof$full_make_init_semantics` for the initial lab
state of the HOL proof (lines 1440-1550): `labst = make_init mc ffi t m
((heap_stack_dm ∪ bitmaps_dm) ∩ byte_aligned) (sdm ∩ byte_aligned) ms lprog ...` with the
stack-to-lab program `lprog` of `compile_prog_max` and the constant oracles of the
HOL proof. Assembled from stage A3a (`panToTargetLabstFacts`), stage A3b
(`panToTargetMemoryAssumption`) over `pan_installed`'s components, and
`backend_config_ok`'s `max_stack_alloc` bound. -/
theorem panToTargetFullMakeInitAssumptions {width : Nat} [NeZero width] {S Q F C : Type}
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
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let biw := StackRemove.bytesInWord width
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
      (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) →
    Assumptions c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset bitmaps p labst
      (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (ltc, [], [])) := by
  intro regNames r1 r2 biw heapStackDm sp maxHeap labst hpi
  have good : goodDimindex width := hmc.1
  obtain ⟨hl, hpc, hio, hcc, hmd, hsmd, hgc, hgco, hsp, hsave, n4, n3, n2, n1, n0, hbij,
    hnf⟩ := panToTargetLabstFacts (C := C) c mc ffi t m
      (fun w => heapStackDm w || bitmapsDm w) sdm ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
      panCode col wprog bitmaps c'' fs p hcfg hmc hinit hisa hwtw hwts hnodup
  have hma := panToTargetMemoryAssumption (C := C) good regNames mc ffi t m bitmapPtr bitmapsDm
    (fun a => sdm a && holByteAligned a) ms
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
    bytes cbspace
    (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
      mc.target.config.addrOffset sp []))
    bitmaps dataSp hpi
  exact ⟨good, rfl, rfl, hnf, hma, hcfg.2.2.2.2.2.2.2.2.2.2.2.1, hl, hpc, hio, hcc, hmd, hsmd,
    hgc, fun _ => hgco, hsp, hsave, n4, n3, n2, n1, n0, hbij⟩

end Flapjack.Pancake.Proofs.PanToTarget
