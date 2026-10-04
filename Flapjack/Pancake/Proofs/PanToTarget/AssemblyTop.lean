import Flapjack.Pancake.Proofs.PanToTarget.CompileSemanticsStatement
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTopResource
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMachineToLab
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabToTarget
import Flapjack.Pancake.Proofs.PanToWord.CompileProgInstOkLess

/-!
# `pan_to_target_compile_semantics`: final assembly

The complete proof of the statement interface `PanToTargetCompileSemanticsStatement`
(`pan_to_targetProofScript.sml:1257-2506`): `compile_prog_max` and `pan_installed`
are unfolded into the stage inputs; `pan_to_word_every_inst_ok_less` supplies the
instruction validity, the machine-to-lab stage (`lab_to_target` `semantics_compile`)
relates the machine semantics to the lab semantics of the initial lab state, and the
lab-state chain with the resource-limit stage concludes.

Untagged: `PanToTargetCompileSemanticsStatement` is the untagged statement interface
(see its docstring for the recorded `pan_installed` memory-domain carrier gap); the
tag decision for the final theorem belongs to its statement review.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL

open Classical in
/-- The statement interface `PanToTargetCompileSemanticsStatement` holds for every input
(Flapjack proof assembly; the tagged `panToTargetCompileSemantics` below states the HOL
theorem itself). -/
theorem panToTargetCompileSemanticsStatement_proof {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS) :
    PanToTargetCompileSemanticsStatement c mc pan_code bytes bitmaps c' stack_max s ffi ms
      globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start := by
  rintro ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg, hmc,
    hinit, hisa, -, hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign,
    rfl, rfl, hlo, hhi, hheap, hheapLt, hffi, hbe, hffiOk, hinst, hstart, hfail⟩ b hb
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, rfl, hmax⟩ :=
    compileProgMax_some c mc pan_code bytes bitmaps _ stack_max hcomp
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, hpm, hgi, hsdm, a1, a2, a3, hle, hbig, hdisj, m0, m1,
    m2, m3, m4, hstar, hffiN, hmmio⟩ := hinst
  -- `pan_to_word_every_inst_ok_less` (stage .20), from `pancake_good_code`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hao, -, hbo, -⟩ := id hcfg
  have hz := good_dimindex_0w_8w hmc.1
  have hevery := PanToWord.panToWordEveryInstOkLess mc.target.config pan_code _ rfl
    (hbo 0 ⟨hz.2, hz.1⟩) hao hgood
  -- the machine-to-lab stage (`lab_to_target` `semantics_compile`)
  have hA4 := panToTargetMachineLab c mc ffi t m bitmapsDm sdm ms bytes cbspace pan_code col
    wprog bitmaps wconf fs p ltconf hcfg hmc hisa hwtw hwts hlab hnodup hffiOk hgi hffiN hmmio
    hevery
  -- the lab-state chain with the resource-limit stage
  have hres := panToTargetLabSemanticsResource (C := LabToTarget.Config) c mc ffi t m bitmapPtr
    bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf pan_code col wprog
    bitmaps wconf fs p data_sp s start globals_size heap_len stack_max hcfg hmc hinit hisa hwtw
    hwts hmax hnodup (fun a h => hpm a (of_decide_eq_true h)) hgi
    (by funext a; rw [hsdm]; simp only [Bool.decide_and, Bool.decide_eq_true]) ⟨a1, a2, a3, hle, hbig, hdisj, m0, m1, m2, m3, m4, hstar⟩ hbase
    hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen hglobLe hmemaddrs htop hstart hsize hparams
    halloc hcode hglobals hlocals heids heshapes hfail
  have hlabne := extendPrime_singleton_ne_fail _ _ _ hres hfail
  have hb' := hA4 (fun h => hlabne h.symm) b hb
  simp only [extendWithResourceLimitPrimeHOL, if_true] at hb'
  rw [hb']
  exact hres

namespace TopWitness

/-- Canonical roundtrip for the four `panSem` state finite maps named by the theorem
(re-export of the reviewed `PanSemStateFiniteExact` witness). -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end TopWitness

/-- HOL `pan_to_target_compile_semantics` (`pan_to_targetProofScript.sml:1256-1300`).
HOL's free variables are explicit in their order of appearance (typed capture
`pan_to_target_compile_semantics_statement_replay`); every constituent is its reviewed
port (`compile_prog_max`, `pancake_good_code`, `backend_config_ok`, `mc_conf_ok`,
`mc_init_ok`, `pan_installed` with the panSem predicate domains, `read_limits`,
`option_lt`, `extend_with_resource_limit'`, `machine_sem`, `semantics_decls`,
`bytes_in_word`, ...).  `0w <₊ x` and `x ≤₊ y` are unsigned `BitVec` order, `dimword (:α)`
is `2 ^ width`, `dimindex (:α)` is `width`, `shift (:α)` is `wordShiftAmount width`,
`OPTION_ALL (EVERY P)` is the `Option` match, and `machine_sem ⊆ X` is membership for
every machine behaviour.  The `panSem` state's `code`/`locals`/`globals`/`eshapes` are the
reviewed finite-support maps. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_target_compile_semantics"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
      PanSemStateFiniteExact.eshapes])
  (words_as_type_indexed_bitvec)]
theorem panToTargetCompileSemantics {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ms : S)
    (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width) (ffi : HolFfiState σ)
    (cbspace data_sp : Nat) (start : MlS) :
    compileProgMax c mc pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
    pancakeGoodCodeHOL pan_code = true ∧
    distinctParamsHOL (functionsHOL pan_code) ∧
    ((functionsHOL pan_code).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL pan_code < 2 ^ width ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    backendConfigOk mc.target.config c ∧ LabToTarget.mcConfOk mc ∧
    mcInitOk mc.target.config c mc ∧ mc.target.config.isa ≠ .ag32 ∧
    (0 : BitVec width) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL pan_code
       let struct_ctxt := decsStcnamesHOLExact (width := width) [] pan_code
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s pan_code ∧
    heap_len = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8) ∧
    s.topAddr = s.baseAddr + (wordSemBytesInWord : BitVec width) * BitVec.ofNat width heap_len -
      BitVec.ofNat width (globals_size * width / 8) ∧
    globals_size ≤ heap_len ∧
    s.memaddrs = StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heap_len - globals_size) ∧
    holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true ∧
    adj_ptr2 = mc.target.getReg ms mc.lenReg +
      (wordSemBytesInWord : BitVec width) * BitVec.ofNat width StackRemove.maxStackAlloc ∧
    adj_ptr4 = mc.target.getReg ms mc.len2Reg -
      (wordSemBytesInWord : BitVec width) * BitVec.ofNat width StackRemove.maxStackAlloc ∧
    adj_ptr2 ≤ mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.ptr2Reg ≤ adj_ptr4 ∧
    (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (wordSemBytesInWord : BitVec width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) ∧
    (wordSemBytesInWord : BitVec width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
      2 ^ width ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    (match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms
      (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config c mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b :=
  panToTargetCompileSemanticsStatement_proof c mc pan_code bytes bitmaps c' stack_max s ffi ms
    globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start

end Flapjack.Pancake.Proofs.PanToTarget
